import ivy_interp as itp
import ivy_art
import ivy_check as icheck
import ivy_transrel as itr
from sklearn import tree
from sklearn.tree import _tree
from ivy_logic_utils import false_clauses, true_clauses, and_clauses, negate_clauses, Clauses, formula_to_clauses
import logic

# No such assumption as universe cannot be empty <TODO>
# <TODO> support for enumerated sort
# <TODO> dictionary mapping Var to its assigned number
maxUniverse = None

'''
:returns a tuple containing universe and pure state.
	pure state is again a tuple with 2nd element a clause repr that state
'''

def sampleUtil(mod, preclause, fcs, actname):
	'''
	a sample created by using z3 which satsfies preclauses and final condition(fcs) where transtion 
	function is obtained from action corresponding to actname
	'''
	action = mod.actions[actname]
	ag = ivy_art.AnalysisGraph()
	pre = itp.State()
	pre.clauses = preclause
	with itp.EvalContext(check=False): # don't check safety
		post = ag.execute(action, pre, None, actname) # action clauses are added
		history = ag.get_history(post)
		gmc = lambda cls, final_cond: itr.small_model_clauses(cls,final_cond,shrink=True)
		axioms = mod.background_theory()
		return history.satisfy(axioms,gmc,fcs)
		

def sampleNeg(mod, curInv):
	actions = sorted(mod.public_actions)
	lcs = mod.labeled_conjs
	fcs = [icheck.ConjChecker(c) for c in lcs]  # inverts the fmla
	for actname in sorted(actions):
		res = sampleUtil(mod, curInv, fcs, actname)
		if res!=None:
			return res
	return None

def samplePos(mod, curInv, coincide):
	actions = sorted(mod.public_actions)
	lcs = mod.labeled_conjs
	fcs = [icheck.ConjChecker(c,invert=False) for c in lcs]
	negateci, negateCoincide = negate_clauses(curInv), negate_clauses(coincide)
	assert isinstance(negateci, Clauses) and isinstance(negateCoincide, Clauses), "negation causes type change" 
	preclause = and_clauses(negateci, negateCoincide)
	for actname in sorted(actions):
		res = sampleUtil(mod, preclause, fcs, actname)
		if res!=None:
			return res
	return None


def learnWeekestInv(mod, clf):
	'''
	curInv and coincide will be of type ivy_logic_utils.Clauses.
	coincide is a Clause object representing samples which cannot be distinguish by feature set
	'''
	curInv, coincide =  true_clauses(), false_clauses()
	while True:
		sneg = sampleNeg(mod,curInv)
		spos = samplePos(mod,curInv,coincide)
		if spos==None and sneg==None:
			break
		clf.addSample(Sample(spos,'1'))
		clf.addSample(Sample(sneg,'0'))
		curInv, coincide = clf.learn()
	return curInv

def constrFeatSet(mod,maxunv):
	c1, c2 = Var('client', 'c0', 0), Var('client', 'c1', 1) 
	s1 = Var('server', 's0', 0)
	ret = []
	ret.append(Equality(c1,c2))
	ret.append(Function('bool', 'link', c1, s1))
	ret.append(Function('bool', 'link', c2, s1))
	ret.append(Function('bool', 'semaphore', s1))
	return ret


'''
:param mod: ivy_module.Module Object
'''
def learnInv(mod):
	print "<learn> Directed to learning Algorithm"
	cond = True 
	while cond:
		maxunv, isInvInd = icheck.isInvInductive(mod)
		if isInvInd: # its Inductive so nothing to do
			break
		global maxUniverse
		maxUniverse = maxunv
		featureset = constrFeatSet(mod,maxunv)
		clf = Classifier(maxunv, featureset) 
		newInv = learnWeekestInv(mod,clf)
		print "<learn> new Invariant:", newInv
		cond = False # for limiting it to one iteration <TODO> remove
		# <TODO> modify mod

def predToivyFmla(pred):
	if isinstance(pred, Function):
		sorts, terms = [], []
		for arg in pred.args:
			term = predToivyFmla(arg)
			terms.append(term)
			sorts.append(term.sort)
		sorts.append(pred.ivysort())
		func = logic.Const(pred.name,logic.FunctionSort(sorts))
		return logic.Apply(func,terms)
	elif isinstance(pred,Var):
		return logic.Const(pred.name,pred.ivysort())
	elif isinstance(pred,Equality):
		t1, t2 = predToivyFmla(pred.args[0]), predToivyFmla(pred.args[1])
		return logic.Eq(t1,t1)
	elif isinstance(pred,Const):
		assert False, "Const object are not supported yet"

class Universe:
	'''
	Nothing but a dictionary containing values each sort can take in the model
	'''
	def __init__(self, unv):
		self.unv = {}
		for key,values in unv.iteritems():
			for value in values:
				newv = Const(value.sort.name,value.name)
				if key.name in self.unv: # key = sort
					self.unv[key.name].append(newv)
				else:
					self.unv[key.name] = [newv]

	def sizeof(self, sort):
		return len(self.unv.get(sort,[]))

	def keys(self):
		return self.unv.keys()

	def __iter__(self):
		return self.unv

	def __getitem__(self, sort):
		return self.unv[sort]

	def get(self,sort,pos):
		assert sort in self.unv, "sort "+sort+" not in Universe"
		assert pos<len(self.unv[sort]), "pos={}, sort={}, unv[sort]={}".format(pos,sort,self.unv[sort])
		return self.unv[sort][pos]

def enum(len,h, suffix):
	if len==1:
		return [[i]+suffix for i in range(h+1)]
	if h==0:
		return [[0]*len + suffix]
	return enum(len,h-1,suffix)+enum(len-1,h,[h]+suffix)


class Sample:
	''' a Sample refers to the model returned by z3.From a model many samplePoints can be extracted	by iterating through instance variable
	instance variable refers to the value of each universally quantified variable (for eg n1, n2)
	currently doesn't support change in universe.
	'''
	def __init__(self, model, label):
		if model is not None:
			self.unv = Universe(model[0])
			self.validateUnv()
			self.interp = Interpretation(model[1][0][1].fmlas) # for state 0 get fmla in clause object 
			self.label = label
			self.numsort = len(self.unv.keys())
			self.initInstance()

	'''
	: returns : Const object
	'''
	def SolveFormula(self,fmla):
		if isinstance(fmla,Var):
			spos = self.sortpos[fmla.sort]
			return self.unv.get(fmla.sort, self.instance[spos][fmla.num]) # get the number
		if isinstance(fmla, Const):
			if self.interp.lookup(fmla):
				return self.interp.lookup(fmla)
			return fmla
		if isinstance(fmla, Function):
			argval = [self.SolveFormula(arg) for arg in fmla.args]
			lookupFunc = Function(fmla.sort,fmla.name,*argval)
			ret = self.interp.lookup(lookupFunc)
			assert ret!=None, "No interpretation for Func {} \nInterp={}".format(lookupFunc,self.interp)
			return ret
		if isinstance(fmla,Equality):
			t1, t2 = self.SolveFormula(fmla.args[0]), self.SolveFormula(fmla.args[1])
			return Const('bool','1' if t1==t2 else '0')

	def validateUnv(self):
		global maxUniverse
		for key in self.unv.keys():
			assert len(self.unv[key]) <= len(maxUniverse[key]), "sample has bigger univ than maxunv on sort "+key  

	def next(self):
		for i in range(self.numsort):
			if self.pos[i] != len(self.enumeration[i])-1:
				self.pos[i]+=1
				self.instance[i] = self.enumeration[i][self.pos[i]]
				break
			self.pos[i] = 0
			self.instance[i] = self.enumeration[i][self.pos[i]]
			if i == self.numsort-1:
				raise StopIteration
		return self

	def __iter__(self):
		return self


	def initInstance(self):
		'''
		self.instance is a list of list of int. where each element of list represent value of all (universally quantified) variables of a sort
		self.enumeration is a list of list of list (Wow!!). each element of enumeration is list of all instance of a sort
		self.pos is used for next instance. it denotes for a given sort which instance in enumeration does self.instance points to
		to make sense of an instance universe is needed
		'''
		self.instance, self.enumeration, self.pos, self.sortpos = [], [], [], {}
		i = 0
		for sort in self.unv.keys(): # <TODO> check if working.
			size = self.unv.sizeof(sort)
			self.instance.append([0]*size)
			self.enumeration.append(enum(size,size-1,[]))
			self.pos.append(0) # initial value = [0]*len(keys)
			self.sortpos[sort] = i
			i+=1
		assert len(self.pos) == self.numsort, "self.pos has incorrect conf"
		assert len(self.enumeration) == self.numsort, "self.enumeration has incorrect conf"
		assert len(self.instance) == self.numsort, "self.instance has incorrect conf"






class Classifier:

	def __init__(self, unv, featureset):
		self.featureset = featureset # list of predicate
		self.maxunv = unv
		# self.label = [] # each element is 0('false')- or 1('true')+ or
		self.samples = []
		self.posDataPoints = set() # each element is tuple containg values of feature set
		self.negDataPoints = set()
		self.cnflDataPoints = set() # samples which cannot be seperated by feature set
		self.clf = tree.DecisionTreeClassifier()

	def learn(self):
		self.clf.fit(list(self.posDataPoints)+list(self.negDataPoints), ['1']*len(self.posDataPoints)+['0']*len(self.negDataPoints))
		return self.toClauses(), self.conflictToClause()

	def addSample(self,sample):
		'''
		A sample is a model and label. A samplePoint is a model and label with a concrete instance. A sample generally have multiple samplePoints.
		Each samplePoint is then converted to dataPoint which is abstraction of samplePoint by feature set.
		'''
		if hasattr(sample, 'unv'):  # sample is not None
			# universe has already been validated
			self.samples.append(sample)
			for samplePoint in sample:
				dataPoint = tuple([samplePoint.SolveFormula(fmla).val for fmla in self.featureset])
				print "<learn> dataPoint is ", dataPoint
				if sample.label=='1':
					if dataPoint in self.cnflDataPoints or dataPoint in self.posDataPoints:
						continue
					if dataPoint in self.negDataPoints:
						self.cnflDataPoints.add(dataPoint)
						continue
					self.posDataPoints.add(dataPoint)
				else:
					if dataPoint in self.cnflDataPoints or dataPoint in self.negDataPoints:
						continue
					if dataPoint in self.posDataPoints:
						self.posDataPoints.remove(dataPoint)
						self.cnflDataPoints.add(dataPoint)
					self.negDataPoints.add(dataPoint)

	def toClauses(self):
		bintree = self.clf.tree_
		# first we will build a formula and then build a Clause
		def tofmla(node):
			"""node is of type int"""
			if bintree.children_right[node] != bintree.children_left[node]: # not a leaf
				assert bintree.feature[node] != _tree.TREE_UNDEFINED, "parent node uses undefined feature"
				assert isinstance(bintree.feature[node], int), "feature returned is not int"
				feat = self.featureset[bintree.feature[node]] # object of class predicate
				ivyFeat = predToivyFmla(feat)
				fmlaleft = tofmla(bintree.children_left[node]) # <TODO> assert that left is always false
				fmlaright = tofmla(bintree.children_right[node])
				fl = logic.And(logic.Not(ivyFeat),fmlaleft)
				f2 - logic.And(ivyFeat,fmlaright)
				return logic.Or(f1,f2)
			else: # is leaf
				numdata = bintree.value[node][0] # gives number of data points for each class, 0 here because its a unioutput clf
				if numdata[0]!=0:
					assert len(numdata)==1 or numdata[1]==0, "leaf node has mixed data points"
					ntype = self.clf.classes_[0]
				else:
					assert len(numdata)==2, "clf is not a biclass clf"
					ntype = self.clf.classes_[1]
				return logic.And() if ntype=='1' else logic.Or() # and with no argument is true, or with no args is false

		seprfmla = tofmla(0) # 0 is the root of tree
		return Clauses([seprfmla])


	'''
	: returns : A logic formula  
	'''
	def ite(self,dp):
		andArgs = []
		for i in range(len(dp)):
			featval = dp[i]
			feat = predToivyFmla(self.featureset[i])
			if featval=='1':
				andArgs.append(feat)
			else:
				andArgs.append(logic.Not(feat))
		return logic.And(*andArgs)

	def conflictToClause(self):
		assert len(self.cnflDataPoints)==0, "conflicting data points {}".format(self.cnflDataPoints)
		orArgs = [self.ite(dataPoint) for dataPoint in self.cnflDataPoints]
		fmla = logic.Or(*orArgs)
		return Clauses([fmla])
			

class Interpretation:
	"""Contains the values for each relation, function and constant in the model stored as dict"""
	
	'''
	:param fmlas: is a list of formulas (logic.Or/Not/Eq/Apply) depicting value of each relation, function, Constant
	'''
	def __init__(self, fmlas):
		self.valof = {}
		# print "<learn> fmla", str(fmlas)
		for fmla in fmlas:
			tup = self.translate(fmla)
			if tup is None:
				continue
			assert isinstance(tup,tuple), "return from translate was not a tuple"
			assert tup[0] not in self.valof, "repeated key formed via translate"
			self.valof[tup[0]] = tup[1]


	def translate(self,fmla):
		if isinstance(fmla, logic.Or): # this info is captured by universe Itself
			return None				   # No need for redundant data
		if isinstance(fmla, logic.Apply):
			args = [self.translate(term) for term in fmla.terms]
			retsort = fmla.func.sort.range.name
			func = Function(retsort,fmla.func.name, *args)
			if retsort=='bool':
				return (func,Const('bool', '1'))
			return (func,None)
		if isinstance(fmla, logic.Const):
			return Const(fmla.sort.name,fmla.name)
		if isinstance(fmla, logic.Eq):
			term1 = self.translate(fmla.t1)
			term2 = self.translate(fmla.t2)
			if isinstance(term1, tuple): # apply was there
				return (term1[0], term2) # <TODO> assertions
			elif term1 is None or term2 is None:
				return None
			return (term1,term2)  # Const is eq some term
		if isinstance(fmla,logic.Not):
			arg = self.translate(fmla.body)
			if isinstance(arg, tuple):
				if isinstance(arg[0], Function): # of the form not(apply)
					return (arg[0], Const('bool', '0'))
				return None #  val1 != val2  No need to interpret this
			assert False, "argument to Not should result in tuple"
		if isinstance(fmla, logic.Var):
			return None  # describes universe, No need to interpret
		assert False, "type "+str(type(fmla))+" has no translation defined"
	
	'''
	: param term: can only be of type Function or Const
	: returns : object of type Const or None  
	'''
	def lookup(self,term):
		return self.valof.get(term, None)

	def __repr__(self):
		return str(self.valof)


class Predicate:

	def __init__(self):
		self.sort = ""

	def ivysort(self):
		return logic.BooleanSort() if pred.sort=='bool' else logic.UninterpretedSort(pred.sort)


class Var(Predicate):
	'''Is used to represent elements in instance only'''
	# leaf
	def __init__(self,sort, name, num):
		self.sort = sort # str
		self.name = name
		self.num = num
	def __repr__(self):
		return self.sort+":"+self.name

	def __hash__(self):
		return hash((self.sort,self.name, self.num))

	def __eq__(self, other):
		return (self.sort,self.name, self.num) == (other.sort,other.name, other.num)



class Const(Predicate):
	#leaf
	def __init__(self,sort,val, name=None):
		self.sort = sort
		self.val = val  # gen a str
		self.name = name
	def __repr__(self):
		return self.sort+":Const("+self.val+")"

	def __hash__(self):
		return hash((self.sort,self.name, self.val))

	def __eq__(self, other):
		return (self.sort,self.name, self.val) == (other.sort,other.name, other.val)


'''
:param args: a list of Predicate(generally Const) 
'''
class Function(Predicate):
	def __init__(self,sort,name,*args):
		self.sort = sort # return sort
		self.name = name
		self.args = args # list of predicate

	def __repr__(self):
		return self.name+"("+",".join(repr(arg) for arg in self.args)+")"

	def __hash__(self):
		# print "<learnp> types", type(self.sort), type(self.name), type(tuple(self.args)) 
		# print "<learnp> type ", type(self.args), self.args
		return hash((self.sort,self.name, self.args ))

	def __eq__(self, other):
		return (self.sort,self.name, self.args) == (other.sort,other.name, other.args)

class Relation(Predicate):
	def __init__(self,name,*args):
		self.sort = 'bool' # TODO verify from interp
		self.name = name
		self.args = args

	def __repr__(self):
		return self.name+"("+",".join(repr(arg) for arg in self.args)+")"

	def __hash__(self):
		return hash((self.sort,self.name, self.args))

	def __eq__(self, other):
		return (self.sort,self.name, self.args) == (other.sort,other.name, other.args)


class Equality(Relation):  # <Note> equality is a relation. Check for breakdown
	def __init__(self,arg1,arg2):
		self.sort = 'bool'
		self.name = 'Eq'
		self.args = [arg1,arg2]

	def __repr__(self):
		return repr(args[0])+" = "+repr(args[1])

	def __hash__(self):
		return hash((self.sort,self.name, self.args))

	def __eq__(self, other):
		return (self.sort,self.name, self.args) == (other.sort,other.name, other.args)



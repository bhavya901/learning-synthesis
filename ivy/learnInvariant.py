import ivy_interp as itp
import ivy_art
import ivy_check as icheck
import ivy_transrel as itr
import sklearn.tree
from sklearn.tree import _tree
from ivy_logic_utils import false_clauses, true_clauses, and_clauses, negate_clauses, Clauses, formula_to_clauses
import logic

# No such assumption as universe cannot be empty
# <TODO> support for enumerated sort
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
    	axioms = im.module.background_theory()
    	return history.satisfy(axioms,gmc,fcs)
    	

def sampleNeg(mod, curInv):
	actions = sorted(im.module.public_actions)
	lcs = mod.labeled_conjs
    fcs = [icheck.ConjChecker(c) for c in lcs]  # inverts the fmla
	for actname in sorted(checked_actions):
        res = sampleUtil(mod, curInv, fcs, actname)
        if res!=None:
        	return res
    return None

def samplePos(mod,curInv, coincide)
	actions = sorted(im.module.public_actions)
	lcs = mod.labeled_conjs
    fcs = [icheck.ConjChecker(c,invert=False) for c in lcs]
	negateci, negateCoincide = negate_clauses(curInv), negate_clauses(coincide)
    assert isInstance(negateci, Clauses) and isInstance(negateCoincide, Clauses), "negation causes type change" 
	preclause = and_clauses(negateci, negateCoincide)
	for actname in sorted(checked_actions):
		res = sampleUtil(mod, preclause, fcs, actname)
		if res!=None:
    		return res
    return None


def learnWeekestInv(mod, clf);
	'''
	curInv and coincide will be of type ivy_logic_utils.Clauses.
	coincide is a Clause object representing samples which cannot be distinguish by feature set
	'''
	curInv, coincide =  true_clauses(), false_clauses()
	while True:
		sneg = sampleNeg(mod,curInv)
		spos = samplePos(mod,curInv,coincide)
		if spos==None and sneg==None:
		clf.addSample(Sample(spos,'1'))
		clf.addSample(Sample(sneg,'0'))
		curInv, coincide = clf.learn()
	return curInv


'''
:param mod: ivy_module.Module Object
'''
def learnInv(mod):
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
		cond = False # for limiting it to one iteration <TODO> remove
		# <TODO> modify mod

class Universe:
	'''
	Nothing but a dictionary containing values each sort can take in the model
	'''
	def __init__(self, unv):
		self.unv = {}
		for key,values in unv.iteritems():
			for value in values
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

	def get(self,sort,pos):
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
			validateUnv()
			self.interp = Interpretation(model[1][1]) 
			self.label = label
			self.numsort = len(self.unv.keys())
			self.initInstance()

	'''
	: returns : Const object
	'''
	def SolveFormula(self,fmla):
		if isInstance(fmla,Var):
			spos = sortpos[fmla.sort]
			return self.unv.get(fmla.sort, spos)
		if isInstance(fmla, Const):
			if self.interp.lookup(fmla):
				return self.interp.lookup(fmla)
			return fmla
		if isInstance(fmla, Function):
			argval = [SolveFormula(arg) for arg in fmla.args]
			lookupFunc = Function(fmla.sort,fmla.name,argval)
			return self.interp.lookup(lookupFunc)
		if isInstance(fmla,Equality):
			t1, t2 = SolveFormula(fmla.args[0]), SolveFormula(fmla.args[1])
			return Const('bool','1' if t1==t2 else '0')

	def validateiUnv(self):
		global maxUniverse
		for key in self.unv.keys():
			assert len(self.unv[key]) <= len(maxUniverse[key]), "sample has bigger univ than maxunv on sort "+key  

	def next(self):
		for i in range(numsort):   
			if self.pos[i] != len(self.enumeration[i])-1:
				self.pos[i]+=1
				self.instance[i] = self.enumeration[i][self.pos[i]]
				break
			self.pos[i] = 0
			self.instance[i] = self.enumeration[i][self.pos[i]]
			if i == len(numsort)-1:
				raise StopIteration
		return self

	def __iter__(self):
		return self


	def initInstance(self):
		'''
		self.instance is a list of list. where each element represent value of all (universally quantified) variables of a sort
		self.enumeration is a list of list of list (Wow!!). each element of enumeration is list of all instance of a sort
		self.pos is used for next instance
		to make sense of an instance universe is needed
		'''
		self.instance, self.enumeration, self.pos, self.sortpos = [], [], [], {}
		i = 0
		for sort in self.unv.keys(): # <TODO> check if working.
			size = self.unv.sizeof(sort)
			self.instance.append([0]*size)
			self.enumeration.append(enum(size,size-1,[]))
			self.pos.append(0) # initial value = [0]*len(leys)
			self.sortpos[sort] = i
			i+=1
		assert len(self.pos) == self.numsort, "self.pos has incorrect conf"
		assert len(self.enumeration) == self.numsort, "self.enumeration has incorrect conf"
		assert len(self.instance) == self.numsort, "self.instance has incorrect conf"



def predToivyFmla(pred):
	if isInstance(pred, Function):
		sorts, terms = [], []
		for arg in pred.args:
			term = predToivyFmla(arg)
			terms.append(term)
			sorts.append(term.sort)
		sorts.append(pred.ivysort())
		func = logic.Const(pred.name,logic.FunctionSort(sorts))
		return logic.Apply(func,terms)
	elif isInstance(pred,Var):
		return logic.Const(pred.name,pred.ivysort())
	elif isInstance(pred,Eq):
		t1, t2 = predToivyFmla(pred.args[0]), predToivyFmla(pred.args[1])
		return logic.Eq(t1,t1)
	elif isInstance(pred,Const):
		assert False, "Const object are not supported yet"


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

	def learn():
		clf.fit(list(self.posDataPoints)+list(self.negDataPoints), ['1']*len(self.posDataPoints)+['0']*len(self.negDataPoints))
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
			 	dataPoint = (samplePoint.SolveFormula(fmla).val for fmla in self.featureset)
			 	if sample.label=='1':
			 		if dataPoint in self.cnflDataPoints or dataPoint in self.posDataPoints:
			 			continue
			 		if dataPoint in self.negDataPoints:
			 			cnflDataPoints.add(dataPoint)
			 			continue
			 		posDataPoints.add(dataPoint)
			 	else:
			 		if dataPoint in self.cnflDataPoints or dataPoint in negDataPoints:
			 			continue
			 		if dataPoint in self.posDataPoints:
			 			posDataPoints.remove(dataPoint)
			 			cnflDataPoints.add(dataPoint)
			 		negDataPoints.add(dataPoint)

	def toClauses(self):
		bintree = clf.tree_
		# first we will build a formula and then build a Clause
		def tofmla(node):
			"""node is of type int"""
			if bintree.children_right[node] != bintree.children_left[node]: # not a leaf
				assert bintree.feature[node] != _tree.TREE_UNDEFINED, "parent node uses undefined feature"
				assert isInstance(bintree.feature[node], int), "feature returned is not int"
				feat = self.featureset[bintree.feature[node]] # object of class predicate
				ivyFeat = predToivyFmla(feat)
				fmlaleft = tofmla(bintree.children_left[node])
				fmlaright = tofmla(bintree.children_right[node])
				fl = logic.And(logic.Not(ivyFeat),fmlaleft)
				f2 - logic.And(ivyFeat,fmlaright)
				return logic.Or(f1,f2)
			else: # is leaf
				numdata = bintree.value[node][0] # gives number of data points for each class, 0 here because its a unioutput clf
				if numdata[0]!=0:
					assert numdata[1]==0, "leaf node has mixed data points"
					ntype = clf._classes_[0]
				else:
					assert numdata[0]==0, "leaf node has mixed data points"
					ntype = clf._classes_[1]
				return logic.And() if ntype=='1' else logic.Or() # and with no argument is true, or with no args is false

		seprfmla = tofmla(0) # 0 is the root of tree
		return Clauses(seprfmla)


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
		return logic.And(andArgs)

	def conflictToClause(self):
		orArgs = [self.ite(dataPoint) for dataPoint in self.cnflDataPoints]
		fmla = logic.Or(orArgs)
		return Clauses(fmla)
			

class Interpretation:
	"""Contains the values for each relation, function and constant in the model stored as dict"""
	
	'''
	:param fmlas: is a list of formulas (logic.Or/Not/Eq/Apply) depicting value of each relation, function, Constant
	'''
	def __init__(self, fmlas):
		self.valof = {}
		for fmla in fmlas:
			tup = self.translate(fmla)
			if tup is None:
				continue
			assert isInstance(tup,tuple), "return from translate was not a tuple"
			assert tup[0] not in self.valof, "repeated key formed via translate"
			self.valof[tup[0]] = tup[1]


	def translate(self,fmla):
		if isInstance(fmla, logic.Or): # this info is captured by universe Itself
			return None				   # No need for redundant data
		if isInstance(fmla, logic.Apply):
			args = [translate(term) for term in fmla.terms]
			retsort = fmla.func.sort.range.name
			func = Function(retsort,fmla.func.name, args)
			if retsort=='bool':
				return (func,Const('bool', '1'))
			return (func,None)
		if isInstance(fmla, logic.Const):
			return Const(fmla.sort,fmla.name)
		if isInstance(fmla, logic.Eq):
			term1 = translate(fmla.t1)
			term2 = translate(fmla.t2)
			if isInstance(term1, tuple): # apply was there
				return (term1[0], term2) # <TODO> assertions
			return (term1,term2)
		if instance(fmla,logic.Not)
			arg = translate(fmla.body)
			if isInstance(arg, tuple):
				if isInstance(arg[0], Function): # of the form not(apply)
					return (arg[0], Const('bool', '0'))
				return None #  val1 != val2  No need to interpret this
			assert False, "argument to Not should result in tuple"
		assert False, "type "+str(type(fmla))+" has no transtion defined"
	'''
	: param term: can only be of type Function or Const
	: returns : object of type Const or None  
	'''
	def lookup(self,term):
		return self.valof.get(term,None)


class Predicate:

	def __init__(self):
		self.sort = ""

	def ivysort(self):
		return logic.BooleanSort() if pred.sort=='bool' else logic.UninterpretedSort(pred.sort)


class Var(Predicate):
	'''Is used to represent elements in instance only'''
	# leaf
	def __init__(self,sort, name)
		self.sort = sort # str
		self.name = name   # str gen a number

	def __repr__(self):
		return self.sort+":n"+self.num



class Const(Predicate):
	#leaf
	def __init__(self,sort,val, name=None):
		self.sort = sort
		self.val = val
		self.name = name
	def __repr__(self):
		return self.sort+":Const("+self.num+")"


'''
:param args: a list of Predicate(generally Const) 
'''
class Function(Predicate):
	def __init__(self,sort,name,*args):
		self.sort = sort # return sort
		self.name = name
		self.args = args # list of predicate

	def __repr__(self):
		return self.name+"("+",".join([repr(arg) for arg in self.args])+")"

class Equality(Relation):  # <Note> equality is a relation. Check for breakdown
	def __init__(self,arg1,arg2):
		self.sort = 'bool'
		self.name = 'Eq'
		self.args = [arg1,arg2]

class Relation(Predicate):
	def __init__(self,name,*args):
		self.sort = 'bool' # TODO verify from interp
		self.name = name
		self.args = args

	def __repr__(self):
		return self.name+"("+",".join([repr(arg) for arg in self.args])+")"


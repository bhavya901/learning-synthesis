'''
Important abbreviations:
	fmla = Formula
	lcs = labeled clauses
	fcs = final Conditions
	clf = classifier
	mod = module
	pred = predicate 
'''



import ivy_interp as itp
import ivy_art
import ivy_check as icheck
import ivy_transrel as itr
from sklearn import tree
from sklearn.tree import _tree
from ivy_logic_utils import false_clauses, true_clauses, and_clauses, negate_clauses, Clauses, formula_to_clauses
import ivy_logic_utils as lut
import logic
from logic import BooleanSort
import ivy_ast
import display_sample as ds

# No such assumption as universe cannot be empty <TODO>
# <TODO> support for enumerated sort
# <TODO> dictionary mapping Var to its assigned number
# <TODO> action Clause for positive sample is different from Neg sample
maxUniverse = None
module = None
candInv = true_clauses()
coincide = false_clauses()
silent = False # if True then silent the print statement in sat checking backend

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


def sampleNeg(mod, candInv):
	actions = sorted(mod.public_actions)
	lcs = mod.labeled_conjs
	conjs = [Clauses([lc.formula]) for lc in lcs]
	fcs = [icheck.ConjChecker(c) for c in lcs]  # inverts the fmla
	preclause = and_clauses(candInv, *conjs)
	for actname in sorted(actions):
		# print "<plearn> checking for action- ", actname
		res = sampleUtil(mod, preclause, fcs, actname)
		# a = raw_input('tried for neg sample')
		if res is not None:
			return res
	return None

def samplePos(mod, candInv, coincide):
	actions = sorted(mod.public_actions)
	lcs = mod.labeled_conjs
	conjs = [Clauses([lc.formula]) for lc in lcs]
	fcs = [icheck.ConjChecker(c,invert=False) for c in lcs]
	negateci, negateCoincide = negate_clauses(candInv), negate_clauses(coincide)
	assert isinstance(negateci, Clauses) and isinstance(negateCoincide, Clauses), "negation causes type change" 
	preclause = and_clauses(negateci, negateCoincide, *conjs)
	for actname in sorted(actions):
		# print "<plearn> checking for action+ ", actname
		res = sampleUtil(mod, preclause, fcs, actname)
		# a = raw_input('tried for pos sample')
		if res is not None:
			return res
	return None


def learnWeekestInv(mod, clf):
	'''
	candInv and coincide will be of type ivy_logic_utils.Clauses.
	coincide is a Clause object representing samples which cannot be distinguish by feature set
	'''
	global candInv, coincide
	candInv, coincide =  true_clauses(), false_clauses()
	while True:
		spos, sneg = samplePos(mod,candInv,coincide), sampleNeg(mod,candInv)
		if spos is None and sneg is None:
			break
		spos, sneg = Sample(spos,'1'), Sample(sneg,'0')
		# print "Positive Sample: ",spos.interp if hasattr(spos, 'interp') else None
		# print "Neg Sample", sneg.interp if hasattr(sneg, 'interp') else None
		if hasattr(spos, 'interp'):
			spos.displaySample()
		if hasattr(sneg, 'interp'):
			sneg.displaySample()	
		clf.addSample(spos)
		clf.addSample(sneg)
		# print "<plearn> done adding samples"
		import sys
		sys.stdout.flush()
		candInv, coincide = clf.learn()
		print "<plearn> candidate Invariant", candInv
		# print "coincide Clause", coincide
		# a = raw_input('One iteration of loop completed, press enter:')
	return candInv


'''
:param mod: ivy_module.Module Object produced after parsing input program
'''
def learnInv(mod):
	print "\n"*2
	print "<plearn> Directed to learning Algorithm"
	global silent
	silent = True
	while True:
		print "Checking Inductiveness of the Invariant"
		maxunv, isInvInd = icheck.isInvInductive(mod)
		print "Invariant is{} Inductive\n".format('' if isInvInd else ' NOT')
		if isInvInd: # its Inductive so nothing to do
			silent = False
			checkInitialCond(mod)
			break
		global maxUniverse, module
		maxUniverse = maxunv
		featureset = constrFeatSetCS(mod,maxunv)
		print "Feature space = {" + ",".join(repr(feat) for feat in featureset)+"}"
		modifyfcs(mod)
		# testfunc(mod)
		module = mod
		clf = Classifier(maxunv, featureset)
		print "learning Invariant"
		newInv = learnWeekestInv(mod,clf)
		print "\n"*2
		print "<plearn> new Invariant:", newInv
		a = raw_input('new Invariant learned, press enter to continue')
		print "\n"*2
		lf = ivy_ast.LabeledFormula(*[ivy_ast.Atom('learnedInv'), logic.And(*newInv.fmlas)])
		mod.labeled_conjs.append(lf)  # modifying mod

def checkInitialCond(mod):
    print "\nChecking if Initialization establishes the learned invariants"
    print "\n    Invariants are: "
    for lc in mod.labeled_conjs:
    	print "    {}".format(Clauses([lc.formula]))
    print ''
    with itp.EvalContext(check=False):
        ag = ivy_art.AnalysisGraph(initializer=lambda x:None)
        icheck.check_conjs_in_state(mod,ag,ag.states[0])


def testfunc(mod):
	lcs = mod.labeled_conjs
	print [lc.formula for lc in lcs]
	exit(0)


def modifyfcs(mod):
	''' fcs = final conditions
	'''
	lcs = mod.labeled_conjs
	for lc in lcs:	
		vars = lut.used_variables_clauses(lc.formula)
		# <TODO> replace vars such that corresponding quantified vars can be identified

def constrFeatSetCS(mod,maxunv):
	c0, c1 = Var('client', 'Client0', 0), Var('client', 'Client1', 1) 
	s0 = Var('server', 'Server0', 0)
	ret = []
	ret.append(Equality(c0,c1))
	ret.append(Function('bool', 'link', c0, s0))
	ret.append(Function('bool', 'link', c1, s0))
	ret.append(Function('bool', 'semaphore', s0))
	return ret

def constrFeatSetLE(mod,maxunv):
	n0,n1 = Var('node', 'Node0', 0), Var('node','Node1', 1)
	id0, id1 = Function('id', 'idn', n0), Function('id', 'idn', n1) 
	ret = []
	ret.append(Equality(n0,n1))
	ret.append(Equality(id0,id1))
	ret.append(Function('bool', 'leader', n0))
	ret.append(Function('bool', 'leader', n1))
	ret.append(Function('bool', 'pending', id0, n0))
	ret.append(Function('bool', 'pending', id1, n1))
	ret.append(Function('bool', 'pending', id0, n1))
	ret.append(Function('bool', 'pending', id1, n0))
	ret.append(Function('bool', 'le', id0, id1))
	ret.append(Function('bool', 'le', id1, id0))
	return ret
	n2 = Var('node', 'Node0', 2)
	id2 = Function('id', 'idn', n2)
	ret.append(Equality(n0,n2))
	ret.append(Equality(n1,n2))
	ret.append(Equality(id0,id1))
	ret.append(Equality(id0,id2))
	ret.append(Equality(id2,id1))
	ret.append(Function('bool', 'leader', n2))
	ret.append(Function('bool', 'pending', id0, n2))
	ret.append(Function('bool', 'pending', id1, n2))
	ret.append(Function('bool', 'pending', id2, n1))
	ret.append(Function('bool', 'pending', id2, n0))
	ret.append(Function('bool', 'pending', id2, n2))
	ret.append(Function('bool', 'le', id1, id2))
	ret.append(Function('bool', 'le', id0, id2))
	ret.append(Function('bool', 'btw', n0, n1, n2))


def predToivyFmla(pred):
	if isinstance(pred, Function):
		sorts, terms = [], []
		for arg in pred.args:
			term = predToivyFmla(arg)
			terms.append(term)
			sorts.append(term.sort)
		sorts.append(pred.ivysort())
		func = logic.Const(pred.name,logic.FunctionSort(*sorts))
		return logic.Apply(func,*terms)
	elif isinstance(pred,Var):   # Var in feature set is universally quantified
		return logic.Var(pred.name,pred.ivysort())
	elif isinstance(pred,Equality):
		t1, t2 = predToivyFmla(pred.args[0]), predToivyFmla(pred.args[1])
		return logic.Eq(t1,t2)
	elif isinstance(pred,Const):
		assert False, "Const object are not supported yet"
	assert False, "Can't Convert {} to ivy formula".format(pred)


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
	''' a Sample refers to the model returned by z3.From a model many samplePoint can be extracted	by iterating through instance variable
	instance variable refers to the value of each universally quantified variable (for eg n1, n2)
	currently doesn't support change in universe.
	'''
	def __init__(self, model, label):
		if model is not None:
			self.unv = Universe(model[0])
			# print "<plearn>",self.unv.unv
			# self.validateUnv()
			self.interp = Interpretation(model[1][0][1].fmlas) # for state 0 get fmla in clause object
			self.poststateItp = Interpretation(model[1][1][1].fmlas) # interpretaion of state resulted by performing action on state 0 
			self.label = label
			self.numsort = len(self.unv.keys())
			self.initInstance()
			# print "<plearn> interpretation", self.interp


	'''
	: param fmla: an ivy predicate logic
	: returns : logic.Const object
	'''
	def solveIvyfmla(self,fmla):
		''' Uses instance and universe to solve the formula
			for positive sample it uses prestate interpretaion, for neg sample it uses post state interprestation
		'''
		if isinstance(fmla, logic.Not):
			res = self.solveIvyfmla(fmla.body)
			assert isinstance(res.sort, logic.BooleanSort), "Not bidy does not returns boolean value"
			return logic.Const('0' if res.name=='1' else '1', BooleanSort())
		if isinstance(fmla, logic.Or):
			solveTerms = [self.solveIvyfmla(t) for t in fmla]
			assert all([term.sort==BooleanSort() for term in solveTerms]), "Or terms should be boolean"
			val = '1' if any([term.name=='1' for term in solveTerms]) else '0'
			return logic.Const(val,BooleanSort())
		if isinstance(fmla, logic.And):
			solveTerms = [self.solveIvyfmla(t) for t in fmla]
			assert all([term.sort==BooleanSort() for term in solveTerms]), "And terms should be boolean"
			val = '1' if all([term.name=='1' for term in solveTerms]) else '0'
			return logic.Const(val,BooleanSort())
		if isinstance(fmla, logic.Eq):
			st1, st2 = self.solveIvyfmla(fmla.t1), self.solveIvyfmla(fmla.t2)
			return logic.Const('1' if st1 == st2 else '0', BooleanSort())
		if isinstance(fmla, logic.Apply):
			solveTerms = [self.solveIvyfmla(t) for t in fmla.terms]
			assert all([isinstance(term, logic.Const) for term in solveTerms]), "apply terms should be Const"
			# print "<plearn> solveTerms:", [t.sort for t in solveTerms]
			args = [Const.toConst(t) for t in solveTerms]
			retsort = fmla.func.sort.range.name
			lookupfunc = Function(retsort,fmla.func.name, *args)
			interp = self.interp if self.label=='1' else self.poststateItp 
			ret = interp.lookup(lookupfunc)
			assert ret!=None, "No interpretation for Func {} \nInterp={}".format(lookupFunc,interp)
			return ret.toivy()
		if isinstance(fmla, logic.Const): # required that quantified var in form __<sortname><id>, id is unique and starts with 0, Sortname should be capitalises
			name = fmla.name
			sort = fmla.sort.name
			assert name.startswith('__'), "non skolemized const"
			assert name[2:len(sort)+2].lower()==sort.lower(), "Const ({},{}) not in desired format".format(fmla.name,fmla.sort.name)
			num = int(name[len(sort)+2:])
			spos = self.sortpos[sort]
			ret = self.unv.get(sort, self.instance[spos][num])
			# print "<plearn> lookup answer", ret
			return ret.toivy()
		if isinstance(fmla, logic.Implies):
			t1, t2 = self.solveIvyfmla(fmla.t1), self.solveIvyfmla(fmla.t2)
			assert t1.sort==BooleanSort() and t2.sort==BooleanSort() and t1.name in ['0','1'], "implies term is not of type Boolean"
			val = '1' if t1.name=='0' or t2.name=='1' else '0'
			return logic.Const(val, BooleanSort())
		assert False, "{} type is not supported".format(type(fmla))
	
	'''
	: returns : Const object
	'''
	def solveFormula(self,fmla):
		if isinstance(fmla,Var):
			spos = self.sortpos[fmla.sort]
			return self.unv.get(fmla.sort, self.instance[spos][fmla.num]) # get the number
		if isinstance(fmla, Const):
			if self.interp.lookup(fmla):
				return self.interp.lookup(fmla)
			return fmla
		if isinstance(fmla, Function):
			argval = [self.solveFormula(arg) for arg in fmla.args]
			lookupFunc = Function(fmla.sort,fmla.name,*argval)
			ret = self.interp.lookup(lookupFunc)
			assert ret!=None, "No interpretation for Func {} \nInterp={}".format(lookupFunc,self.interp)
			return ret
		if isinstance(fmla,Equality):
			t1, t2 = self.solveFormula(fmla.args[0]), self.solveFormula(fmla.args[1])
			return Const('bool','1' if t1==t2 else '0')

	def validateUnv(self):
		global maxUniverse
		for key in self.unv.keys():
			assert len(self.unv[key]) <= len(maxUniverse[key]), "sample has bigger univ than maxunv on sort "+key  


	def addto(self, sortnum):
		inst = self.instance[sortnum] # python copies list by reference
		sort = self.sortat[sortnum]
		for i in range(len(inst)):
			if inst[i]==self.unv.sizeof(sort)-1:
				inst[i] = 0  
			else:
				inst[i] += 1
				return True
		return False


	def next(self):
		if not self.hasIterated:
			self.hasIterated = True
			return self
		for i in range(self.numsort):
			if self.addto(i):
				return self
			if i == self.numsort-1:
				raise StopIteration

	def __iter__(self):
		return self

	
	def isValid(self):
		''' Checks if the current instance is a valid samplePoint
			Assumptions : safety Condition and Candidate Inv is Universally Quantified.
		'''
		global module, candInv, coincide
		if self.label == '0':
			fcs = [icheck.ConjChecker(c) for c in module.labeled_conjs]  # inverts the fmla
			fmlas = [fc.cond().fmlas for fc in fcs] # fc.cond().fmlas gives a list of ivy predicate logic. 
		else:
			return True # It will cause repeatation of some positive samples, but it will not change the correctness of algorithm 
			negateci, negateCoincide = negate_clauses(candInv), negate_clauses(coincide)
			condition = and_clauses(negateci, negateCoincide)
			fmlas = [condition.fmlas]
			print "<plearn> printing condition to check valid positive samplePoint", condition
		for fmla in fmlas: # requires to satisfy atleast one fmla
			isfmlatrue = True
			for pred in fmla:
				ret = self.solveIvyfmla(pred)
				assert isinstance(ret,logic.Const), "return value is not a Const object"
				assert isinstance(ret.sort, BooleanSort), "return is not a boolean formla"
				assert ret.name in ["0", "1"], "return value is not in correct format"
				# print "<plearn> pred: {} \t\t result: {}".format(pred, ret.name)
				if ret.name == "0":
					isfmlatrue = False
					break
			if isfmlatrue:
				return True
		return False



	def initInstance(self):
		'''
		self.instance is a list of list of int. where each element of list represent value of all (universally quantified) variables of a sort
		self.enumeration is a list of list of list (Wow!!). each element of enumeration is list of all instance of a sort
		self.pos is used for next instance. it denotes for a given sort which instance in enumeration does self.instance points to
		to make sense of an instance universe is needed
		'''
		global maxUniverse
		self.instance, self.enumeration, self.pos, self.sortpos, self.sortat = [], [], [], {}, []
		i = 0
		for sort in self.unv.keys(): # <TODO> check if working.
			instsize = maxUniverse.sizeof(sort) # size of the instance depends of maxUniverse or feature set to be exact
			size = self.unv.sizeof(sort)
			self.instance.append([0]*instsize)
			# self.enumeration.append(enum(instsize,size-1,[]))
			# self.pos.append(0) # initial value = [0]*len(keys)
			self.sortpos[sort] = i
			self.sortat.append(sort)
			i+=1
		# assert len(self.pos) == self.numsort, "self.pos has incorrect conf"
		# assert len(self.enumeration) == self.numsort, "self.enumeration has incorrect conf"
		assert len(self.instance) == self.numsort, "self.instance has incorrect conf"
		self.hasIterated = False


	def displaySample(self):
		state0 = ds.getGraph(self.unv, self.interp)
		state1 = ds.getGraph(self.unv, self.poststateItp)
		ds.displayStates(self.label, state0, state1)


class Classifier:

	def __init__(self, unv, featureset):
		self.featureset = featureset # list of object of class Predicate
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
		A sample is a model and label. A samplePoint is a model and label with a concrete instance. A sample generally have multiple samplePoint.
		Each samplePoint is then converted to dataPoint which is abstraction of samplePoint by feature set i.e. value of features.
		'''
		if hasattr(sample, 'unv'):  # sample is not None
			# universe has already been validated
			print "<plearn> {} sample will be added".format("+" if sample.label=='1' else "-")
			self.samples.append(sample)
			newPoints = []
			for samplePoint in sample:
				# print "<plearn> {} samplePoint instance {}".format("+" if sample.label=='1' else "-", samplePoint.instance)
				if not samplePoint.isValid():
					continue
				dataPoint = tuple([samplePoint.solveFormula(fmla).val for fmla in self.featureset])
				# print "<plearn> dataPoint is ", dataPoint
				if sample.label=='1':
					if dataPoint in self.cnflDataPoints or dataPoint in self.posDataPoints:
						continue
					if dataPoint in self.negDataPoints:
						self.cnflDataPoints.add(dataPoint)
						continue
					self.posDataPoints.add(dataPoint)
					newPoints.append(dataPoint)
				else:
					if dataPoint in self.cnflDataPoints or dataPoint in self.negDataPoints:
						continue
					if dataPoint in self.posDataPoints:
						self.posDataPoints.remove(dataPoint)
						self.cnflDataPoints.add(dataPoint)
					self.negDataPoints.add(dataPoint)
					newPoints.append(dataPoint)
			print "New {} sample points added = {}".format("+" if sample.label=='1' else "-", newPoints)			


	def toClauses(self):
		bintree = self.clf.tree_
		# first we will build a formula and then build a Clause
		def tofmla(node):
			"""node is of type int"""
			if bintree.children_right[node] != bintree.children_left[node]: # not a leaf
				assert bintree.feature[node] != _tree.TREE_UNDEFINED, "parent node uses undefined feature"
				assert isinstance(bintree.feature[node], int), "feature returned is not int"
				feat = self.featureset[bintree.feature[node]] # object of class Predicate
				ivyFeat = predToivyFmla(feat)
				fmlaleft = tofmla(bintree.children_left[node]) # <TODO> assert that left is always false
				fmlaright = tofmla(bintree.children_right[node])
				if fmlaright==logic.And():
					return simplifyOr(ivyFeat, fmlaleft)
				if fmlaleft==logic.And():
					return simplifyOr(logic.Not(ivyFeat), fmlaright)
				f1 = simplifyAnd(logic.Not(ivyFeat),fmlaleft)
				f2 = simplifyAnd(ivyFeat,fmlaright)
				return simplifyOr(f1,f2)
			else: # is leaf
				numdata = bintree.value[node][0] # gives number of data points for each class, 0 here because its a unioutput clf
				if numdata[0]!=0:
					assert len(numdata)==1 or numdata[1]==0, "leaf node has mixed data points"
					ntype = self.clf.classes_[0]
				else:
					assert len(numdata)==2 and numdata[1]!=0, "clf is not a biclass clf"
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
		# assert len(self.cnflDataPoints)==0, "conflicting data points {}".format(self.cnflDataPoints)
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
		# print "<plearn> fmla", str(fmlas)
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
		return logic.BooleanSort() if self.sort=='bool' else logic.UninterpretedSort(self.sort)


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

	@classmethod
	def toConst(cls, obj):
		return cls(obj.sort.name, obj.name)

	def __repr__(self):
		return self.sort+":Const("+self.val+")"

	def __str__(self):
		return self.sort[:3]+str(self.val)

	def __hash__(self):
		return hash((self.sort,self.name, self.val))

	def __eq__(self, other):
		return (self.sort,self.name, self.val) == (other.sort,other.name, other.val)

	def toivy(self):
		return logic.Const(self.val, BooleanSort() if self.sort=='bool' else logic.UninterpretedSort(self.sort))

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

	def arity(self):
		return len(self.args)

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
		return repr(self.args[0])+" = "+repr(self.args[1])

	def __hash__(self):
		return hash((self.sort,self.name, self.args))

	def __eq__(self, other):
		return (self.sort,self.name, self.args) == (other.sort,other.name, other.args)



def simplifyAnd(f1, f2):
	if f2==logic.Or() or f1==logic.Or():
		return logic.Or()
	if f2==logic.And():
		return f1
	return logic.And(f1,f2)

def simplifyOr(f1, f2):
	if f2==logic.And() or f1==logic.And():
		return logic.And()
	if f2==logic.Or():
		return f1
	return logic.Or(f1,f2)
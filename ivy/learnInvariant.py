'''
Important abbreviations:
	fmla = Formula # mainly used to denote ivy predicate logic, but is also used to denote object of class Predicate defined in learnInvariant
	lcs = labeled clauses
	fcs = final Conditions = conjectures + invariant + prev learned Invariant 
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
import ivy_utils as iu

# <TODO> No such assumption as universe cannot be empty
# <TODO> support for enumerated sort
# <TODO> dictionary mapping Var to its assigned number
# <TODO> action Clause for positive sample is different from Neg sample
module = None
featureset = []
numVarFS = {} # number of Variables(quant.) of each sort in feature set (invariant: equal to max number of quantified Var that could be present in CandInv)
numVarInv = {} # number of variables of each sort in learned as well as previous invariant. Used for determining instance size
candInv = true_clauses()
coincide = false_clauses()
silent = False # if True then silent the print statement in sat checker (ivy backend)
enum = iu.BooleanParameter("enum",False)

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
		post = ag.execute(action, pre, None, actname) # action clauses are added to preclause here (transition function and preclause)
		history = ag.get_history(post)
		gmc = lambda cls, final_cond: itr.small_model_clauses(cls,final_cond,shrink=True) #shrink=True gives smallest possible sample
		axioms = mod.background_theory()
		return history.satisfy(axioms,gmc,fcs)


def sampleNeg(mod, candInv, actname):
	lcs = mod.labeled_conjs
	conjs = [Clauses([lc.formula]) for lc in lcs]
	fcs = [icheck.ConjChecker(c) for c in lcs]  # also negates the fmla
	preclause = and_clauses(candInv, *conjs)
	# print "<plearn> checking for action- ", actname
	res = sampleUtil(mod, preclause, fcs, actname)
	# print candInv
	# a = raw_input('tried for neg sample')
	return res

def samplePos(mod, candInv, coincide, actname):
	lcs = mod.labeled_conjs
	conjs = [Clauses([lc.formula]) for lc in lcs]
	fcs = [icheck.ConjChecker(c,invert=False) for c in lcs]
	negateci, negateCoincide = negate_clauses(candInv), negate_clauses(coincide)
	assert isinstance(negateci, Clauses) and isinstance(negateCoincide, Clauses), "negation causes type change" 
	preclause = and_clauses(negateci, negateCoincide, *conjs)
	print "preclause: ",preclause
	print "not coincide: ", negateCoincide
	# print "<plearn> checking for action+ ", actname
	res = sampleUtil(mod, preclause, fcs, actname)
	a = raw_input('tried for pos sample')
	return res

def learnWeekestInv(mod, clf, actname):
	'''
	candInv and coincide will be of type ivy_logic_utils.Clauses.
	coincide is a Clause object representing samples which cannot be distinguish by feature set
	'''
	global candInv, coincide
	candInv, coincide =  true_clauses(), false_clauses()
	while True:
		spos = samplePos(mod,candInv,coincide, actname) # Generating positve sample
		sneg = sampleNeg(mod,candInv, actname)
		if spos is None and sneg is None:
			break
		spos, sneg = Sample(spos,'1'), Sample(sneg,'0') 
		print "Pos Sample", spos.unv.unvsize() if hasattr(spos, 'interp') else None
		print "Neg Sample", sneg.unv.unvsize() if hasattr(sneg, 'interp') else None
		# if hasattr(spos, 'interp'): # spos is not None
		# 	print "<plearn> + sample interpretation : ",spos.interp, "\n" # for detailed information
		# 	spos.displaySample() # for displaying the sample
		# if hasattr(sneg, 'interp'): # sneg is not None
			# print "<plearn> - sample interpretation : ",sneg.interp, "\n" # for detailed information
			# sneg.displaySample()
		clf.addSample(spos) # adding Positive sample
		clf.addSample(sneg)
		print "<plearn> done adding samples"
		import sys
		sys.stdout.flush()
		candInv, coincide = clf.learn()
		print "<plearn> candidate Invariant", candInv
		sys.stdout.flush()
		# print "coincide Clause", coincide
		# a = raw_input('One iteration of loop completed, press enter:')
	return candInv


'''
:param mod: ivy_module.Module Object produced after parsing input program
'''
def learnInv(mod):
	print "\n"*2
	print "<plearn> Directed to learning Algorithm"
	global silent, module, numVarFS, featureset
	silent = True
	updatenvi(mod)
	module = mod
	while True:
		print "Checking Inductiveness of the Invariant"
		maxunv, isInvInd = icheck.isInvInductive(mod)
		print "Invariant is{} Inductive\n".format('' if isInvInd else ' NOT')
		if isInvInd: # its Inductive so nothing to do
			silent = False
			checkInitialCond(mod)
			break
		# testfunc(mod)
		for actname in sorted(mod.public_actions):
			print "learning Invariant for action {}".format(actname)
			clf = Classifier() # new classifier
			newInv = learnWeekestInv(mod,clf, actname)
			print "\n"*2
			print "<plearn> new Invariant:", newInv
			a = raw_input('new Invariant learned, press enter to continue')
			print "\n"*2
			numVarFS = {} # resetting numVarFS
			featureset = [] # resetting featuerset
			if newInv != true_clauses():
				lf = ivy_ast.LabeledFormula(*[ivy_ast.Atom('learnedInv'+actname), logic.And(*newInv.fmlas)])
				mod.labeled_conjs.append(lf)  # modifying mod and module, obj are copied by refr.
				updatenvi(mod) # takes care of numVarInv

def checkInitialCond(mod):
	print "\nChecking if Initialization establishes the learned invariants"
	print "\n    Invariants are: "
	for lc in mod.labeled_conjs:
		print "    {}".format(Clauses([lc.formula]))
	print ''
	with itp.EvalContext(check=False):
		ag = ivy_art.AnalysisGraph(initializer=lambda x:None)
		lcs = mod.labeled_conjs
		fcs = [icheck.ConjChecker(c) for c in lcs]
		history = ag.get_history(ag.states[0])
		gmc = lambda cls, final_cond: itr.small_model_clauses(cls,final_cond,shrink=True)
		axioms = mod.background_theory()
		model = history.satisfy(axioms,gmc,fcs)
		smpl = Sample(model, '-1') # this sample has no post state
		if hasattr(smpl, 'interp'): # smpl is not None
			print "<plearn> + sample interpretation : ",smpl.interp, "\n" # for detailed information
			smpl.displaySample() # for displaying the sample
			print "\nInitialization establishes the learned Invariant: FAIL"
		else:
			print "\nInitialization establishes the learned Invariant: PASS"


def testfunc(mod):
	# for testing/ debugging
	ns = logic.UninterpretedSort("node")
	ids = logic.UninterpretedSort('id')
	n1 = logic.Var('Node0', ns)
	n2 = logic.Var('Node1', ns)
	ineq = logic.Not(logic.Eq(n2,n1))
	leadsorts = [ns, logic.BooleanSort()]
	leadfunc = logic.Const("leader",logic.FunctionSort(*leadsorts))
	idsorts = [ns, logic.UninterpretedSort("id")]
	idfunc = logic.Const("idn", logic.FunctionSort(*idsorts))
	lesorts = [ids, ids, logic.BooleanSort()]
	lefunc = logic.Const('le', logic.FunctionSort(*lesorts))
	leadterm = logic.Apply(leadfunc, *[n1])
	leterm = logic.Apply(lefunc,*[logic.Apply(idfunc, *[n1]), logic.Apply(idfunc, *[n2])])
	fmla = logic.Not(logic.And(*[ineq, leadterm, leterm]))
	candInv, coincide = Clauses([fmla]), false_clauses()
	print "<plearn> CandInv", candInv
	for actname in sorted(mod.public_actions):
		spos, sneg = samplePos(mod,candInv,coincide, actname), sampleNeg(mod,candInv, actname)
		spos, sneg = Sample(spos,'1'), Sample(sneg,'0')
		if hasattr(spos, 'interp'):
			print "<plearn> + interp: ",spos.interp
			spos.displaySample()
		if hasattr(sneg, 'interp'):
			print "<plearn> - interp: ",sneg.interp
			sneg.displaySample()
	exit(0)



def updatenvi(mod):
	''' nvi = NumVarInv
		it just calculates the number of quantified variables of each sort in the fcs.
	'''
	lcs = mod.labeled_conjs
	varsof = {}
	for lc in lcs:
		quant_vars = lut.used_variables_clauses(lc.formula) # list
		# print "var in conjs", quant_vars
		# <TODO> replace vars such that corresponding quantified vars can be identified
		for var in quant_vars:
			sort = var.sort.name
			name = var.name
			if sort not in varsof.keys():
				varsof[sort] = set([name])
			else:
				varsof[sort].add(name)
	global numVarInv
	for sort in varsof.keys():
		numVarInv[sort] = len(varsof[sort])


def constrFeatSet(newNumVarFS):
	if newNumVarFS.get('node',0)!=0:
		constrFeatSetLE(newNumVarFS)
	else:
		constrFeatSetCS(newNumVarFS)

def constrFeatSetLE(newNumVarFS):
	''' for leader election program
	'''
	global module, numVarFS
	if newNumVarFS['node'] != newNumVarFS['id']:
		assert False, "thats odd" # comment this if stmt if you expect this behaviour
	if newNumVarFS['node']>=1 and numVarFS.get('node',0)<1:
		constrFeatSetLE1()
	if newNumVarFS['node']>=2 and numVarFS['node']<2:
		constrFeatSetLE2()
	if newNumVarFS['node']>=3 and numVarFS['node']<3:
		constrFeatSetLE3()
	if newNumVarFS['node']>=4:
		assert False, "numVarFS = {}".format(numVarFS) 	# leader election having counterexample of 4 or more nodes

def constrFeatSetCS(newNumVarFS):
	''' for client server program
	'''
	global module, numVarFS
	if newNumVarFS['client']>=1 and numVarFS.get('client',0)<1:
		constrFeatSetCS11()
	if newNumVarFS['client']>=2 and numVarFS['client']<2:
		constrFeatSetCS21()
	if newNumVarFS['server']>=2 and numVarFS['server']<2:
		constrFeatSetCS12()
	if newNumVarFS['server']>=2 and newNumVarFS['client']>=2:
		constrFeatSetCS22()
	if newNumVarFS['server']>2 or newNumVarFS['client']>2:
		assert False,  "numVarFS = {}".format(numVarFS) 	# client server having counterexample of nodes than necessary


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
	Nothing but a dictionary where key = sort name (str)
	value = list of values (Const(Predicate) obj) each sort can take in the model
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
		return sorted(self.unv.keys())
	
	def unvsize(self):
		ret = {}
		for sort in self.keys():
			ret[sort] = self.sizeof(sort)
		return ret

	def __iter__(self):
		return self.unv

	def __getitem__(self, sort):
		return self.unv[sort]

	def get(self,sort,pos):
		assert sort in self.unv, "sort "+sort+" not in Universe"
		assert pos<len(self.unv[sort]), "pos={}, sort={}, unv[sort]={}".format(pos,sort,self.unv[sort])
		return self.unv[sort][pos]

	def __repr__(self):
		return repr(self.unv)


class Sample:
	''' a Sample refers to the model returned by z3. From a model many samplePoint can be extracted	by iterating through instance variable
	instance variable refers to the value of each universally quantified variable (for eg n1, n2)
	in simple terms model = universe + interpretation. model with self.hasIterated being false is Sample. model + self.instance = samplePoint
	to get different samplePoint vary the self.instance by calling next. 
	'''
	def __init__(self, model, label):
		if model is not None:
			self.unv = Universe(model[0])
			# self.validateUnv()
			self.interp = Interpretation(model[1][0][1].fmlas) # for state 0 get fmla in clause object (pre state interpretation)
			if label!='-1': # not the counter example generated from failed initialization check  
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
		if isinstance(fmla, logic.Or): # short circuit
			for term in fmla:
				sterm = self.solveIvyfmla(term)
				assert sterm.sort==BooleanSort(), "Or terms should be boolean"
				if sterm.name=='1':
					return logic.Const('1',BooleanSort())
			return logic.Const('0',BooleanSort())
		if isinstance(fmla, logic.And): # short circuit
			for term in fmla:
				sterm = self.solveIvyfmla(term)
				assert sterm.sort==BooleanSort(), "Or terms should be boolean"
				if sterm.name=='0':
					return logic.Const('0',BooleanSort())
			return logic.Const('1',BooleanSort())
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
			# print "debug: instance = {}, spos={}, num={}".format(self.instance,spos,num)
			ret = self.unv.get(sort, self.instance[spos][num])
			# print "<plearn> lookup answer", ret
			return ret.toivy()
		if isinstance(fmla, logic.Implies): # short circuit
			t1 = self.solveIvyfmla(fmla.t1)
			assert t1.sort==BooleanSort() and t1.name in ['0','1'], "implies term1 is not of type Boolean" 
			if t1.name=='0':
				return logic.Const('1', BooleanSort()) 
			t2 = self.solveIvyfmla(fmla.t2)
			assert t2.sort==BooleanSort() and t2.name in  ['0','1'], "implies term2 is not of type Boolean"
			val = '1' if t2.name=='1' else '0'
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


	def addto(self, sortnum):
		s_inst = self.instance[sortnum] # python copies list by reference
		assert isinstance(s_inst, list), "instance's element is not a list"
		sort = self.sortat[sortnum]
		for i in range(len(s_inst)):
			if s_inst[i]==self.unv.sizeof(sort)-1:
				s_inst[i] = 0  
			else:
				s_inst[i] += 1
				return True
		return False


	def next(self):
		''' called during for loop iteration to generate new instance
		'''
		if not self.hasIterated:
			self.hasIterated = True
			return self
		for i in range(self.numsort):
			if self.addto(i):
				return self
			if i == self.numsort-1: # <bhavya> for leader election only
				raise StopIteration

	def __iter__(self):
		return self

	
	def isValid(self):
		''' Checks if the current instance is a valid samplePoint. 
			i.e. for negative sample it checks if the samplePoint satisfies negation of current invariant (fcs) in post state
			Assumptions : safety Condition and Candidate Inv and Coincide clause is Universally Quantified.
		'''
		global module, candInv, coincide
		if self.label == '0': # nagative sample
			fcs = [icheck.ConjChecker(c) for c in module.labeled_conjs]  # inverts the fmla
			fmlas = [fc.cond().fmlas for fc in fcs] # fc.cond().fmlas gives a list of ivy predicate logic object.
		else: # positive sample
			# return True # It will cause repeatation of some positive samples, but it will not affect the correctness of algorithm 
			# comment the above return stmt to check validity of positive samples 
			negateci, negateCoincide = negate_clauses(candInv), negate_clauses(coincide)
			condition = and_clauses(negateci, negateCoincide)
			fmlas = [condition.fmlas]
			# assert len(fmlas) == 1, "" 
		for fmla in fmlas: # requires satisfying atleast one fmla, as they are in disjunction 
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
		self.instance is a list of list of int. where each element of self.instance represent value of all (universally quantified) variables of a sort
		to make sense of an instance universe is needed.
		for eg if self.instance['node'][1] = 0 then value of Node1 is self.unv.get('node','0') which would usually be node:Const(0) Const(Predicate) object
		instance along with universe is used to calculate the value of predicate in featureset and checking validity of samplePoint
		'''
		global numVarFS, numVarInv
		self.instance, self.enumeration, self.pos, self.sortpos, self.sortat = [], [], [], {}, []
		i = 0
		for sort in sorted(self.unv.keys(), reverse=True):
			instsize = max(numVarFS.get(sort,0), numVarInv.get(sort,0)) # size of the instance depends on feature set and Previous Invariant size (for validation)
			self.instance.append([0]*instsize)
			self.sortpos[sort] = i # constant
			self.sortat.append(sort) # constant
			i+=1
		assert len(self.instance) == self.numsort, "self.instance has incorrect conf"
		self.hasIterated = False


	def displaySample(self):
		state0 = ds.getGraph(self.unv, self.interp)
		state1 = ds.getGraph(self.unv, self.poststateItp) if self.label!='-1' else None
		ds.displayStates(self.label, state0, state1)

	def setInstance(self, inst):
		self.instance = inst


class Classifier:

	def __init__(self):
		self.posSamples = []
		self.negSamples = []
		self.posDataPoints = set() # each element is tuple containg values of feature set
		self.negDataPoints = set()
		self.cnflDataPoints = set() # samples which cannot be seperated by feature set
		self.clf = tree.DecisionTreeClassifier()

	def learn(self):
		self.clf.fit(list(self.posDataPoints)+list(self.negDataPoints), ['1']*len(self.posDataPoints)+['0']*len(self.negDataPoints)) #sklearn library
		return self.toClauses(), self.conflictToClause()

	def addSample(self,sample):
		'''
		A sample is a model + label (object of class Sample). A samplePoint is a model + label(= Sample) with a concrete instance (sample.instance denoting some meaningful value)(object of class Sample).
		A sample generally have multiple samplePoint. difference between two samplePoint belonging to same sample is only in instance variable i.e. values of quantified variable.
		As samplePoint has value of each quantified variable we can get value of each predicates in feature set to get dataPoint. 
		Each samplePoint is then converted to dataPoint which is abstraction of samplePoint by feature set i.e. value of features.
		'''
		global featureset
		if hasattr(sample, 'unv'):  # sample is not None
			print "<plearn> {} sample will be added".format("+" if sample.label=='1' else "-")
			self.updateFeatSet(sample) # checks and update if feature set update is needed
			newPoints = []
			self.posSamples.append(sample) if sample.label=='1' else self.negSamples.append(sample)
			for samplePoint in sample:
				# print "<plearn> {} samplePoint instance {}".format("+" if sample.label=='1' else "-", samplePoint.instance)
				if not samplePoint.isValid():
					continue
				dataPoint = tuple([samplePoint.solveFormula(fmla).val for fmla in featureset])
				# print "<plearn> dataPoint is ", dataPoint
				if sample.label=='1': # positve sample
					if dataPoint in self.cnflDataPoints or dataPoint in self.posDataPoints:
						continue
					if dataPoint in self.negDataPoints:
						self.cnflDataPoints.add(dataPoint)
						continue
					self.posDataPoints.add(dataPoint)
					newPoints.append(dataPoint)
					if not enum.get(): # do not enumerate, translates to stop when first dataPoint is found
						print "sample.instance: ", samplePoint.instance
						break
				else: # negative sample
					if dataPoint in self.cnflDataPoints or dataPoint in self.negDataPoints:
						continue
					if dataPoint in self.posDataPoints:
						self.posDataPoints.remove(dataPoint)
						self.cnflDataPoints.add(dataPoint)
					self.negDataPoints.add(dataPoint)
					newPoints.append(dataPoint)
					if not enum.get():
						print "sample.instance: ", samplePoint.instance
						break
			print "New {} sample points added = {}".format("+" if sample.label=='1' else "-", newPoints)


	def toClauses(self):
		''' converts decision tree to Clause. 
		'''
		bintree = self.clf.tree_  # the underlying decision tree of clf
		# first we will build a formula and then build a Clause
		def tofmla(node):
			''' encodes the subtree with root represented by node to fmla
				node is of type int
			'''
			global featureset
			if bintree.children_right[node] != bintree.children_left[node]: # not a leaf
				assert bintree.feature[node] != _tree.TREE_UNDEFINED, "parent node uses undefined feature"
				assert isinstance(bintree.feature[node], int), "feature returned is not int"
				threshold = bintree.threshold[node]
				assert not (threshold == 0 or threshold==1), "threshold=({}, {}) adds no information".format(type(threshold), threshold) 
				feat = featureset[bintree.feature[node]] # object of class Predicate
				ivyFeat = predToivyFmla(feat)
				fmlaleft = tofmla(bintree.children_left[node]) # left branch means case when ivyFeat is false
				fmlaright = tofmla(bintree.children_right[node])
				if fmlaright==logic.And(): # fmlaright == True
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


	def updateFeatSet(self, sample):
		global numVarFS
		# if positive sample or sample universe less than quantified Var in featSet for all sort then do nothing
		if sample.label=='1' or all(sample.unv.sizeof(sort) <= numVarFS.get(sort,0) for sort in sample.unv.keys()):
			return
		newNumVarFS = {} 
		for sort in sample.unv.keys():
			newNumVarFS[sort] = max(sample.unv.sizeof(sort), numVarFS.get(sort, 0))
		print "<plearn> updating featureSet vars to", newNumVarFS
		constrFeatSet(newNumVarFS) # also changes numVarFS
		global featureset
		print "<plearn> featureset is ", featureset
		sample.initInstance()
		self.posDataPoints, self.negDataPoints, self.cnflDataPoints = set(), set(), set() # empty out previous dataPoints
		for smpl in self.negSamples:
			smpl.initInstance() # this initiates the new instance according to updated feature set, (changes instance size acc. to newNumVarFS)
			for samplePoint in smpl: # enumerating through all samplePoints according to updated instance
				if not samplePoint.isValid():
					continue
				dataPoint = tuple([samplePoint.solveFormula(fmla).val for fmla in featureset])
				self.negDataPoints.add(dataPoint)
		for smpl in self.posSamples:
			smpl.initInstance()	# same here
			for samplePoint in smpl: # same enumeration
				dataPoint = tuple([samplePoint.solveFormula(fmla).val for fmla in featureset])
				if dataPoint in self.cnflDataPoints or dataPoint in self.posDataPoints:
					continue
				if dataPoint in self.negDataPoints:
					# print "<plearn> confl samplePoint:", samplePoint.interp
					self.cnflDataPoints.add(dataPoint)
					continue
				self.posDataPoints.add(dataPoint)
		print "<plearn> update completed"

	'''
	: param dp : dataPoint
	: returns : A logic formula  
	'''
	def ite(self,dp):
		global featureset
		andArgs = []
		for i in range(len(dp)):
			featval = dp[i]
			feat = predToivyFmla(featureset[i])
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
	"""Contains the values for each relation, function and constant in the model stored as dict
		explained for client server program:
		for eg. on abstract level interpretaion will contain value of leader(node:Const(0)) as either bool:Const(0) (# false) or bool:Const(1) (# true)
		similarly it will have value of pending(id:Const(0), node:Const(1)) as either bool:Const(0) (# false) or bool:Const(1) (# true)
		similarly it will have value of idn(node:Const(0)) as some Const(Predicate) object (for eg id:Const(1))
		in short interpretation has value of all relation, function (that are in the input program) for all arguments. 
	"""
	
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
		''' this function acts as a parser which parses the fmla in state interpretation returned by ivy
			returns either None (no extra info or redundant info) or a tuple
		'''
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
	'''Is used to represent elements in instance only
		Used to represent universally quantifued variables
	'''
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
	def __init__(self,sort,val, name=None):
		self.sort = sort
		self.val = val  # generally a str
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
	# redundant as of now, all relations are modeled as function wih return type bool
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
	if f1==logic.And():
		return f2
	return logic.And(f1,f2)

def simplifyOr(f1, f2):
	if f2==logic.And() or f1==logic.And():
		return logic.And()
	if f2==logic.Or():
		return f1
	if f1==logic.Or():
		return f2
	return logic.Or(f1,f2)



def constrFeatSetCS11():
	global numVarFS, featureset
	c0 = Var('client', 'Client0', 0)
	s0 = Var('server', 'Server0', 0)
	numVarFS['client'] = 1
	numVarFS['server'] = 1
	featureset.append(Function('bool', 'link', c0, s0))
	featureset.append(Function('bool', 'semaphore', s0))

def constrFeatSetCS21():
	''' upgrade number of clients to 2, with 1 server
	'''
	global numVarFS, featureset
	c0, c1 = Var('client', 'Client0', 0), Var('client', 'Client1', 1) 
	s0 = Var('server', 'Server0', 0)
	numVarFS['client'] = 2
	numVarFS['server'] = 1
	featureset.append(Equality(c0,c1))
	featureset.append(Function('bool', 'link', c1, s0))

def constrFeatSetCS12():
	global numVarFS, featureset
	c0 = Var('client', 'Client0', 0) 
	s0, s1 = Var('server', 'Server0', 0), Var('server', 'Server1', 1)
	numVarFS['client'] = 1
	numVarFS['server'] = 2
	featureset.append(Equality(s0,s1))
	featureset.append(Function('bool', 'link', c0, s1))
	featureset.append(Function('bool', 'semaphore', s1))

def constrFeatSetCS22():
	global numVarFS, featureset
	c0, c1 = Var('client', 'Client0', 0), Var('client', 'Client1', 1) 
	s0, s1 = Var('server', 'Server0', 0), Var('server', 'Server1', 1)
	numVarFS['client'] = 2
	numVarFS['server'] = 2
	featureset.append(Function('bool', 'link', c1, s1))

def constrFeatSetLE1():
	global numVarFS, featureset
	n0 = Var('node', 'Node0', 0)
	id0 = Function('id', 'idn', n0)
	numVarFS['node'] = 1
	numVarFS['id'] = 1
	featureset.append(Function('bool', 'leader', n0))

def constrFeatSetLE2():
	global numVarFS, featureset
	n0,n1 = Var('node', 'Node0', 0), Var('node','Node1', 1)
	id0, id1 = Function('id', 'idn', n0), Function('id', 'idn', n1) 
	numVarFS['node'] = 2
	numVarFS['id'] = 2
	featureset.append(Equality(n0,n1))
	featureset.append(Equality(id0,id1))
	featureset.append(Function('bool', 'leader', n1))
	featureset.append(Function('bool', 'pending', id0, n0))
	featureset.append(Function('bool', 'pending', id1, n1))
	featureset.append(Function('bool', 'pending', id0, n1))
	featureset.append(Function('bool', 'pending', id1, n0))
	featureset.append(Function('bool', 'le', id0, id1))
	featureset.append(Function('bool', 'le', id1, id0))

def constrFeatSetLE3():
	global numVarFS, featureset
	n0,n1 = Var('node', 'Node0', 0), Var('node','Node1', 1)
	id0, id1 = Function('id', 'idn', n0), Function('id', 'idn', n1)
	n2 = Var('node', 'Node2', 2)
	id2 = Function('id', 'idn', n2)
	numVarFS['node'] = 3
	numVarFS['id'] = 3
	featureset.append(Equality(n0,n2))
	featureset.append(Equality(n1,n2))
	featureset.append(Equality(id0,id2))
	featureset.append(Equality(id1,id2))
	featureset.append(Function('bool', 'leader', n2))
	featureset.append(Function('bool', 'pending', id0, n2))
	featureset.append(Function('bool', 'pending', id1, n2))
	featureset.append(Function('bool', 'pending', id2, n1))
	featureset.append(Function('bool', 'pending', id2, n0))
	featureset.append(Function('bool', 'pending', id2, n2))
	featureset.append(Function('bool', 'le', id1, id2))
	featureset.append(Function('bool', 'le', id0, id2))
	featureset.append(Function('bool', 'ring.btw', n0, n1, n2))
	featureset.append(Function('bool', 'ring.btw', n0, n2, n1))
	featureset.append(Function('bool', 'ring.btw', n1, n0, n2))
	featureset.append(Function('bool', 'ring.btw', n1, n2, n0))
	featureset.append(Function('bool', 'ring.btw', n2, n1, n0))
	featureset.append(Function('bool', 'ring.btw', n2, n0, n1))
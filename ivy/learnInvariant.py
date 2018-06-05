import ivy_interp as itp
import ivy_art
import ivy_check as icheck
import ivy_transrel as itr
from sklearn import tree
from ivy_logic_utils import false_clauses, true_clauses, and_clauses, negate_clauses, Clauses

# No such assumption as universe cannot be empty


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
        	return res  #<TODO> pasing through some function to cnvt into suitable Obj
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
    		return res  #<TODO> pasing through some function to cnvt into suitable Obj
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
			break
		clf.addSample(Sample(spos,1))
		clf.addSample(Sample(sneg,0))
		curInv, coincide = clf.learn()
	return curInv


'''
:param mod: ivy_module.Module Object
'''
def learnInv(mod):
	while True:
		maxunv, isInvInd = icheck.isInvInductive(mod)
		if isInvInd: # its Inductive
			break
		featureset = constrFeatSet(mod,maxunv)
		clf = Classifier(maxunv, featureset) 
		newInv = learnWeekestInv(mod,clf)
		# <TODO> modify mod

class Universe:
	'''
	Nothing but a dictionary containing values for each sort in the model
	'''
	def __init__(self, unv):
		self.unv = {}
		for key,value in unv.iteritems():
			self.unv[key.name] = self.unv[key.name].append(value.name) if key.name in self.unv else [value.name]

	def sizeof(self, sort):
		return len(self.unv.get(sort,[]))

class Sample:
	def __init__(self, model, label):
		if model is not None:
			self.unv = Universe(model[0])
			self.interp = model[1] #<TODO>
			self.label = label

	def SolveFormula(self,fmla,instance):
		pass

	def validateiUnv(instance):
		pass


class Classifier:

	def __init__(self, unv, featureset):
		self.featureset = featureset # list of predicate
		self.maxunv = unv
		self.label = [] # each element is 0('false')- or 1('true')+ or
		self.sample = [] # each element is list containg values of feature set
		self.clf = tree.DecisionTreeClassifier()
		self.conflict = [] # samples which cannot be seperated by feature set

	def learn():
		pass

	def addSample(self,sample):
		if hasattr(sample, 'unv'):  # sample is not None
			pass # <TODO>

	def ToClauses(self):
		pass

	def removeConflict(self):
		pass

	def conflictToClause(self):
		pass


class Predicate:

	def __init__(self):
		self.sort = ""


class Var(Predicate):
	# leaf
	def __init__(self,sort, num)
		self.sort = sort # str
		self.name = name   # str gen a number

	def __repr__(self):
		return self.sort+":n"+self.num

class Const(Predicate):
	#leaf
	def __init__(self,sort,val):
		self.sort = sort
		self.val = val

	def __repr__(self):
		return self.sort+":Const("+self.num+")"

class Relation(Predicate):
	def __init__(self,name,*args):
		self.sort = 'Boolean' # TODO verify from interp
		self.name = name
		self.args = args

	def __repr__(self):
		return self.name+"("+",".join([repr(arg) for arg in self.args])+")"

class Function(Predicate):
	def __init__(self,sort,name,*args):
		self.sort = sort # return sort
		self.name = name
		self.args = args

	def __repr__(self):
		return self.name+"("+",".join([repr(arg) for arg in self.args])+")"

class equality(Relation):
	def __init__(self,arg1,arg2):
		self.sort = 'Boolean'
		self.name = 'Eq'
		self.args = [arg1,arg2]


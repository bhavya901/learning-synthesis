import ivy_interp as itp
import ivy_art
import ivy_check as icheck
import ivy_transrel as itr
from ivy_logic_utils import false_clauses, true_clauses, and_clauses, negate_clauses, Clauses

'''
:returns a tuple containing universe and pure state.
 	pure state is again a tuple with 2nd element a clause repr that state
'''

def sampleUtil(mod, preclause, fcs, actname):
	'''
	a sample created by using z3 which satsfies preclauses and final condition(fcs) where transtion 
	function is obtained from action corressponding to actname
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


def learnWeekestInv(mod);
	'''
	curInv and coincide will be of type ivy_logic_utils.Clauses.
	coincide is a Clause object representing samples which cannot be distinguish by feature set
	'''
	curInv, coincide =  true_clauses(), false_clauses()
	sneg = sampleNeg(mod,curInv)
	spos = samplePos(mod,curInv,coincide)
	while not (spos==None and sneg==None):
		# add to S+
		# add to S-
		# learn

	return curInv
'''
:param mod: ivy_module.Module Object
'''
def learnInv(mod):
	while not icheck.isInvInductive(mod):
		learnWeekestInv(mod)

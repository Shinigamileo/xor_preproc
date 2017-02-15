from satutils import *
from functools import reduce

# int representations of lits are what the solver reads (-1, +1, -2, +2, ...)
# literals are an internal representation from 0..2n (0=1, 1=-1, 2=2, 3=-2, 4=3, 5=-3, ...)
# This is suitable for array indexing
def intToLit(i):
    return ((abs(i)-1) << 1) + (i < 0)

def litToInt(l):
    ''' Function for getting external (user) literals indexing (-N..+N) from internal literal indexing (0..2N-1)'''
    return (l >> 1) + 1 - 2*(l&1)*((l >> 1) + 1)

def varToInt(v): return v+1

# Vars are variable indexes suitable for array indexing (0...n-1)
def varToLit(v, sign=0):
    return (v << 1) + sign

def signLit(l):
    return l%2 

def notLit(l):
    """Given the litteral l, give its negation (x <-> -x)"""
    return l ^ 1

def litToVar(l):
    return l >> 1

def litToVarSign(l):
    return litToVar(l), signLit(l)


############################################################################################
class Clause():
    ''' Very simple clause wrapper.
    TODO: Needs to add a sorting technique for building the clause'''
    literals = None   # Array of literals
    learnt = False    # True if this is a learnt clause
    lbd = 0           # Score introduced in Glucose
    score = 0.0       # CSIDS score (decaying activity score, if used)
    abstraction = 0   # A int that acts as a Bloom filter (when I will use it)
    dll_isSAT = False # True if the clause is SAT under the current partial assignment (used in DLL)

    def __init__(self, listOfLiterals = None, learnt = False, lbd = None):
        self.literals = array('i')
        self.score = 0.0
        self.learnt = learnt
        self.lbd = lbd if lbd is not None else len(listOfLiterals)
        self.dll_isSAT = False
        self.dll_size = len(listOfLiterals)
        if listOfLiterals is not None:
           self.literals.fromlist(sorted(list(set(listOfLiterals))))
        return

    def addLiteral(self, lit):
        self.literals.append(lit)

    def removeLiteral(self, lit):
        self.literals.remove(lit)

    def containsLiteral(self,lit):
        #return self.literals.contains(lit)
        lint = intToLit(lit)
        i = 0
        while i < len(self) and self[i] < lint:
            i+=1
        return i < len(self) and self[i] == lint

    def containsVariable(self,var):
        vant = intToLit(var)
        i = 0
        while i < len(self) and self[i] < vant:
            i+=1
        return i < len(self) and (self[i] == vant or self[i] == vant+1)

    def variables(self):
        res = []
        for i in range(len(self)):
            res.append(abs(litToInt(self[i])))
        return res

    def getK(self,fill):
        s = ""
        filt = '{0:0'+str(fill)+'d} '
        for l in self:
            s += filt.format(abs(litToInt(l)))
        return s

    def incScore(self):
        self.score += self.var_inc

    def getScore(self):
        return self.score

    def _calcAbstraction(self):
        """ Computes a simple Bloom filter for the clause """
        filter = 0
        for i in range(0, len(self)):
            filter &= (self[i] << (i % 64))

    def isUseless(self):
        """Look if a clause is useless, 
        aka if a literal and its opposite are in it"""
        for i in range(len(self)-1):
            if ((self[i+1] == self[i]+1)
                and (self[i+1]%2)):
                return True
        return False

    def polarity(self):
        return reduce(lambda res, l: ( res ^ 1 ^ signLit(l) ),
                      [0] + list(self.literals))


    # We (re)define now some classical Python methods

    def __iter__(self):
        ''' Allows to use the iterator from the array import '''
        return self.literals.__iter__()

    def __str__(self):
        ''' Gets the clause as a list of literals '''
        return ",".join(list(map(lambda l: str(litToInt(l)), self.literals)))

    def __getitem__(self, x):
        return self.literals[x]

    def __setitem__(self, x, itm):
        self.literals[x] = itm

    def __len__(self):
        return len(self.literals)

    def __lt__(self, other):
        return self.score < other.score

    def __eq__(self, other):
        return self.literals == other.literals





if __name__ == '__main__':
    c = Clause([0,2,4,6,8])
    print(str(c) + " --> " + str(c.polarity()))

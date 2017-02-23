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
def var2lit(v, sign=1):
    return 2*v*sign - v

def signLit(l):
    return l>0

def notLit(l):
    """Given the litteral l, give its negation (x <-> -x)"""
    return -l

def litToVar(l):
    return l >> 1

def litToVarSign(l):
    return litToVar(l), signLit(l)


##############################################################################
class Clause():
    ''' Very simple clause wrapper.
    TODO: Needs to add a sorting technique for building the clause'''

    def __init__(self, listOfLiterals = []):
        self.literals = dict()
        self.useless = set()
        for l in listOfLiterals:
            self.addLiteral(l)

    def addLiteral(self, lit):
        var = abs(lit)
        sign = lit/var
        if var in self.literals and self[var] != lit:
            self.useless.add(var)
        self[var] = lit

    def addSwap(self, var, lit):
        if var in self.literals:
            self[var].add( lit )
        else:
            self[var] = set([lit])

    def removeVariable(self, var):
        self.literals.pop(var)

    def containsVariable(self,var):
        return (var in self.literals) and self[var]

    def variables(self):
        return list(self.literals.keys())

    def litterals(self):
        return list(self.literals.values())

    def getK(self,fill=3):
        filt = '{0:0'+str(fill)+'d} '
        return " ".join(list(map(lambda v: filt.format(v),self.variables())))

    def polarity(self):
        return reduce(lambda res, l: ( res ^ 1 ^ signLit(l) ),
                      [1] + self.litterals())

    
    def dimacstr(self):
        return " ".join(list(map(lambda l:str(l),self.litterals()))) + " 0"

    # We (re)define now some classical Python methods

    def __iter__(self):
        return iter(self.literals)
    
    def __str__(self):
        ''' Gets the clause as a list of literals '''
        return ",".join(list(map(lambda l:str(l),self.litterals())))

    def __contains__(self, itm):
        return itm in self.literals

    def __getitem__(self, x):
        return self.literals[x]

    def __setitem__(self, x, itm):
        self.literals[x] = itm

    def __nonzero__(self):
        return not self.useless

    def __len__(self):
        return len(self.literals)

    def __lt__(self, other):
        return self.score < other.score

    def __eq__(self, other):
        return self.literals == other.literals





if __name__ == '__main__':
    c = Clause([0,2,4,6,8])
    print(str(c) + " --> " + str(c.polarity()))

from sattypes import *
from math import *
import random

def random_cnf_clauses(solver,k=3,n=20,m=100):
    random.seed() # Uses system time
    for nc in range(0,m):
        c = []
        while len(c) < k:
            l = (random.randint(1,n)) * (1 if random.randint(0,1) else -1)
            if not l in c and not -l in c:
                c.append(l)
        solver.addClause(c)
    

def readFile(solver, filename):
    """A very python-like parser for CNF files (probably too nested I fear)"""
    starttime = time.time()
    print("c Opening file {f:s}".format(f=filename))
    
    for line in myopen(filename):
        if not line[0] in ['c','p']:
            solver.addClause([l for l in list(map(int,line.split()))
                              if l is not 0]) 

    print("c File readed in {t:03.2f}s".format(t=time.time()-starttime))
    
###########
# XLAUSES #
###########

class Xlause():
    _nbvars = 0
    _xiterals = []

    def __init__(self, nbVars, listOfVars = [], result = 0):
        self._nbvars = nbVars
        self._xiterals = []
        j = 0
        for i in range(nbVars):
            self._xiterals.append(int(j < len(listOfVars)
                                      and  i == listOfVars[j]-1))
            j += self._xiterals[i]
        self._xiterals.append(result)

    def __add__(self, other):
        for i in range(self._nbvars+1):
            self._xiterals[i] ^= other._xiterals[i]
        return self

    def __str__(self):
        for i in range(0,self._nbvars):
            string += (" + " + str(i+1))*self._xiterals[i]
        return string + " = " + str(self._xiterals[self._nbvars])

    def __getitem__(self, x):
        return self._xiterals[x]

    def __setitem__(self, x, itm):
        self.xiterals[x] = itm

    def __len__(self):
        return self._nbvars
    
##############
# XOR SOLVER #
##############

# Au debut, il n'y avait rien.
# Et de ce rien, est ne le SAT-solver
    
class XorSolver():

    _nbvars  = 0   # Number of variables
    _clauses = [] # Clauses
    _xlauses = [] # XOR-Clauses

    def __init__(self):
        self._nbvars = 0
        self._clauses = []
        self._xlauses = []
        return

    def printClauses(self):
        for i in range(len(self._clauses)):
            print(self._clauses[i])

    def addClause(self, listOfInts):
        """Add a clause... that's about it"""
        c = Clause([intToLit(l) for l in listOfInts])
        if not c.isUseless():
            self._clauses.append(c)
            self._nbvars = max(self._nbvars, max(abs(i) for i in listOfInts))

    def addXlause(self, listOfVars):
        self._xlauses.append(Xlause(self._nbvars,listOfVars))

    def sort(self):
        """Sort the clauses according to their variables"""
        fill0 = int(log10(self._nbvars))+1
        self._clauses.sort( key = lambda c: c.getK(fill0) )

    def noDuplicates(self):
        fill0 = int(log10(self._nbvars))+1
        for i in range(len(self._clauses)):
            j = i+1
            while j < len(self._clauses) and\
                  self._clauses[i].getK(fill0) == self._clauses[j].getK(fill0):
                if self._clauses[i] == self._clauses[j]:
                    del(self._clauses[j])
                else:
                    j+=1

    def cute(self):
        self.sort()
        self.noDuplicates()

    def ctox(self):
        """Create the Xlauses from the clauses,
        returns the number of those found"""
        count = 0
        begin = 0
        while begin < len(self._clauses):
            size = 2**(len(self._clauses[begin])-1)
            variables = self._clauses[begin].variables()
            end = begin+1
            while end < len(self._clauses) and\
                  variables == self._clauses[end].variables():
                end+=1
            if end - begin >= size:
                xors = [[],[]]
                for i in range(begin,end):
                    xors[self._clauses[i].polarity()].append(i)
                for k in [0,1]:
                    if len(xors[k]) == size:
                        count += 1
                        for i in range(size):
                            print(self._clauses[xors[k][i]])
                        string = "==> " + str(variables[0])
                        for i in range(1,len(variables)):
                            string += " + " + str(variables[i])
                        print(string + " = " + str(k)+"\n")
            begin = end
        return count
                    
                
        
    def solve(self):
        """IT SOLVES !!!"""
        self.cute()


##############
#            #
#    MAIN    #
#            #
##############

if __name__ == '__main__':
    xolver = XorSolver()
    random_cnf_clauses(xolver,3,10,1000)
    print("")
    print("clauses without sorting :")
    xolver.printClauses()
    xolver.cute()
    print("")
    print("clauses with sorting and no duplicates :")
    xolver.printClauses()
    print("")
    print("Xlauses :")
    print( str(xolver.ctox()) + " Xlause(s) found !" )
    x = Xlause(3,[1,2])
    y = Xlause(3,[2,3])
    print(x)
    print(y)
    exit()
    

from sattypes import *
from math import *
import time, sys, random

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
    
##############
# XOR SOLVER #
##############

# Au debut, il n'y avait rien.
# Et de ce rien, est ne le SAT-solver
    
class XorSolver():

    _nbvars  = 0  # Number of variables
    _clauses = [] # Clauses
    _xlauses = [] # XOR-Clauses
    _xvars   = []
    _tvars   = []

    def __init__(self):
        self._nbvars  = 0
        self._clauses = []
        self._xlauses = []
        self._xvars   = []
        self._tvars   = []
        return

    def printClauses(self):
        for i in range(len(self._clauses)):
            print(self._clauses[i])

    def printXlauses(self):
        for i in range(len(self._xlauses)):
            print(self._xlauses[i])

    def addClause(self, listOfInts):
        """Add a clause... that's about it"""
        c = Clause([intToLit(l) for l in listOfInts])
        if not c.isUseless():
            self._clauses.append(c)
            self._nbvars = max(self._nbvars, max(abs(i) for i in listOfInts))

    def addXlause(self, listOfVars, result):
        xlause = []
        i = 0
        j = 0
        while i < len(self._xvars) and j < len(listOfVars):
            xlause.append(int(listOfVars[j] == self._xvars[i]))
            j += xlause[-1]
            i += 1
        while i < len(self._xvars):
            xlause.append(0)
            i += 1
        self._xlauses.append(BinEquation(xlause,result))

    def _sortingSortSortingThatSorts(self):
        """Sort the clauses according to their variables"""
        fill0 = int(log10(self._nbvars))+1
        self._clauses.sort( key = lambda c: c.getK(fill0) )

    def _noNoDuplicatesNoNoNo(self):
        fill0 = int(log10(self._nbvars))+1
        for i in range(len(self._clauses)):
            j = i+1
            while j < len(self._clauses) and\
                  self._clauses[i].getK(fill0) == self._clauses[j].getK(fill0):
                if self._clauses[i] == self._clauses[j]:
                    del(self._clauses[j])
                else:
                    j+=1

    def sortNset(self):
        self._sortingSortSortingThatSorts()
        self._noNoDuplicatesNoNoNo()

    def ctox(self):
        """Create the Xlauses from the clauses,
        returns the number of those found"""
        count = 0      # The count we commented about the line above. Witness !
        lines2del = [] # The lines which will be removed from the clauses
        xor2add = []   # The lines which will be added to the Xlauses
        cvars = set()  # The variables present in the clauses
        xvars = set()  # The variables present in the Xlauses

        # To begin with, we must gather the Xlauses
        begin = 0
        while begin < len(self._clauses):
            # First, we spotlight the clauses which have
            # the same variables in it
            size = 2**(len(self._clauses[begin])-1)
            variables = self._clauses[begin].variables()
            end = begin+1
            while end < len(self._clauses) and\
                  variables == self._clauses[end].variables():
                end+=1
            # We see if we have enough clauses to do anything
            if end - begin >= size:
                # Then we split the clauses according to their polarity,
                # aka the parity of their number of positive litterals
                xors = [[],[]]
                for i in range(begin,end):
                    xors[self._clauses[i].polarity()].append(i)
                for k in range(2):
                    if len(xors[k]) == size:
                        # if we have enough clause in one of them,
                        # then we found a Xlause !
                        count += 1
                        lines2del += xors[k]
                        xor2add.append([variables,k])
                        xvars |= set(variables)
            else:
                cvars |= set(variables)
            begin = end

        # Now, we can update the self itself, which means :
        # - suppressing the clauses now useless
        for i in sorted(lines2del, reverse=True):
            del self._clauses[i]
        # - writing down the variables in the Xlauses and those only
        self._xvars = sorted(list(xvars))
        self._tvars = sorted(list(xvars - cvars))
        # - fabriquer correctement la matrice sur laquelle on fera des Gauss
        for x in xor2add:
            self.addXlause(x[0],x[1])
                   
        return count

    def bite(self):
        """Sert a faire des Gauss"""
        r = 0
        j = 0
        while r < len(self._xlauses) and j < len(self._xvars):
            k = r
            while k < len(self._xlauses) and not self._xlauses[k][j]:
                k += 1
            if k < len(self._xlauses):
                swap(self._xlauses,r,k)
                for i in range(len(self._xlauses)):
                    if i != r and self._xlauses[i][j]:
                        self._xlauses[i] += self._xlauses[r]
                r += 1
                # print("")
                # self.printXlauses()
            j += 1
            
        

##############
#            #
#    MAIN    #
#            #
##############

if __name__ == '__main__':
    xolver = XorSolver()
    if len(sys.argv) > 1:
        readFile(xolver, sys.argv[1])
    else:
        random_cnf_clauses(xolver,3,5,100)
    print("")
    print("clauses without sorting :")
    xolver.printClauses()
    xolver.sortNset()
    print("")
    print("clauses with sorting and no duplicates :")
    xolver.printClauses()
    print("")
    print("Xlause detection !!!")
    print( str(xolver.ctox()) + " Xlause(s) found !" )
    print("")
    print("Clauses :")
    xolver.printClauses()
    print("")
    print("Xlauses :")
    xolver.printXlauses()
    xolver.bite()
    print("")
    print("Xlauses after getting laid :")
    xolver.printXlauses()
    exit()
    

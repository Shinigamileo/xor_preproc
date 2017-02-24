from mysattypes import *
from math import *
from enum import Enum
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

    def __init__(self):
        self._nbvars       = 0
        self._clauses      = []
        self._xor2add      = []
        self._xornadd      = []
        self._xlauses      = []
        self._xvars        = []
        self._xvarsnb      = []
        self._tvars        = []
        self._learnt       = []
        self._almostlearnt = []
        self._known        = Clause()
        self._almostknown  = Clause()
        self.status        = 0

    def printClauses(self,dimacs=False):
        if dimacs:
            for i in range(len(self._clauses)):
                print(self._clauses[i].dimacstr())
        else:
            for i in range(len(self._clauses)):
                print(self._clauses[i])

    def printXlauses(self):
        for i in range(len(self._xlauses)):
            print(self._xlauses[i])

    def addClause(self, listOfInts):
        """Add a clause... that's about it"""
        c = Clause(listOfInts)
        if not c.useless:
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

    def _Xlause2Clause(self,xlause):
        e = xlause.elements()
        for k in range(2**len(e)):
            if bin(k).count('1')%2 == xlause.result ^ 1:
                clause = Clause()
                for i in range(len(e)):
                    clause.addLiteral(self._xvars[e[i]]*(-1)**(k%2))
                    k //= 2
                self._clauses.append(clause)

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

    def _learningVars(self):
        clauses2del = set()
        count = 0
        if self._almostlearnt:
            for i in range(len(self._clauses)):
                for ls in self._almostlearnt:
                    cv = self._clauses[i].containsVariable(ls[0])
                    if cv:
                        count += 1
                        self._clauses[i].removeVariable(ls[0])
                        self._clauses[i].addLiteral((cv/abs(cv))*ls[1])
                        if self._clauses[i].useless:
                            clauses2del.add(i)
            deleteAll(self._clauses,list(clauses2del))
                

        clauses2del = set()
        for i in range(len(self._clauses)):
            if len(self._clauses[i].variables()) == 1:
                clauses2del.add(i)
                self._learnt.append(self._clauses[i].variables()[0])
        deleteAll(self._clauses,list(clauses2del))


        if self._learnt:
            clauses2del = set()
            for i in range(len(self._clauses)):
                for l in self._learnt:
                    cv = self._clauses[i].containsVariable(abs(l))
                    if cv:
                        count += 1
                        if l == cv:
                            clauses2del.add(i)
                        else:
                            self._clauses[i].removeVariable(abs(l))
                            self.status |= not bool(len(self._clauses[i]))
            deleteAll(self._clauses,list(clauses2del))

        
        for vs in self._almostlearnt:
            self._almostknown.addSwap(abs(vs[1]),var2lit(vs[0],signLit(vs[1])))
        for v in self._learnt:
            self._known.addLiteral(v)
            av = abs(v)
            if av in self._almostknown:
                for l in list(self._almostknown[av]):
                    self._known.addLiteral(av/v*l)
                self._almostknown.removeVariable(av)
        self._almostlearnt = []
        self._learnt = []
        print("c " + str(count) + " clause(s) changed")
        self.status |= bool(self._known.useless)
        return count

    def _gatherXlausesFromClauses(self):
        """Create the Xlauses from the clauses,
        returns the number of those found"""
        count = 0      # The count we commented about the line above. Witness !
        lines2del = [] # The lines which will be removed from the clauses
        cvars = set()  # The variables present in the clauses
        xvars = set()  # The variables present in the Xlauses

        self._xvarsnb = [[] for i in range(self._nbvars)]
        xor2addi = len(self._xor2add)

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
                        self._xor2add.append([sorted(variables),k])
                        xvars |= set(variables)
                        for v in variables:
                            self._xvarsnb[v-1].append(xor2addi)
                        xor2addi += 1
            else:
                cvars |= set(variables)
            begin = end

        # Now, we can update the self itself, which means :
        # - suppressing the clauses now useless
        deleteAll(self._clauses,lines2del)
        # - writing down the variables in the Xlauses and those only
        self._xvars = sorted(list(xvars | set(self._xvars)))
        self._tvars = sorted(list(set(self._xvars) - cvars))
                   
        return count

    

    def _createMatrix(self):
        # print(self._xor2add)
        # print(self._xvarsnb)
        # print(self._tvars)
        # zerefed = []
        # for x in self._tvars:
        #     if len(self._xvarsnb[x-1]) <= 2:
        #         if len(self._xvarsnb[x-1]) == 2:
        #             print(x)
        #             print(self._xor2add[self._xvarsnb[x-1][1]])
        #             self._xor2add[self._xvarsnb[x-1][1]] = [list(set(self._xor2add[self._xvarsnb[x-1][1]][0]) ^ set(self._xor2add[self._xvarsnb[x-1][0]][0])),self._xor2add[self._xvarsnb[x-1][1]][1] ^ self._xor2add[self._xvarsnb[x-1][0]][1]]
        #         self._xornadd.append(self._xvarsnb[x-1][0])
        #         zerefed.append(self._xvarsnb[x-1][0])
        # deleteAll(self._xor2add,zerefed)
        for x in self._xor2add:
            self.addXlause(x[0],x[1])
            # print(str(x) + " => " + str([list(map(lambda l:self._xvars[l],self._xlauses[-1].elements())),self._xlauses[-1].result]))

    def _bite(self):
        """Sert a faire des Gauss"""
        count = 0
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
                        count+=1
                r += 1
            j += 1
        return count

    def _mine(self):
        """Parce que faut bien en faire quelque chose ensuite"""
        for x in self._xlauses:
            e = x.elements()
            le = len(e)
            if not len(e):
                None
                if x.result:
                    self.status = 1
            elif len(e) == 1:
                self._learnt.append(var2lit(self._xvars[e[0]],x.result))
            elif len(e) == 2:
                self._almostlearnt.append([self._xvars[e[0]],
                                           var2lit(self._xvars[e[1]],
                                                   1^x.result)])
            else:
                self._Xlause2Clause(x)

    def _propagate1(self):
        didChange = False
        self._learningVars()
        # while self._learningVars():
        #     didChange = True
        return didChange

    def _buildData2_propagate2(self):
        self._sortingSortSortingThatSorts()
        self._noNoDuplicatesNoNoNo()
        print("c " + str(self._gatherXlausesFromClauses()) + " Xlauses found")
        self._createMatrix()

    def _propagate2(self):
        # print(self._xvars)
        didChange = self._bite() > 0
        # self.printXlauses()
        self._mine()
        self._xlauses = []
        self._xvars = []
        self._xor2add = []
        self._xornadd = []
        return didChange

    def solve(self):
        doContinue = True
        count = 1
        # self.printClauses()
        print("c ////////////////////////////")
        print("c // Propagation no. " + str(count))
        print("c ////////////////////////////")
        self._propagate1()
        while doContinue and not self.status:
            count += 1
            self._buildData2_propagate2()
            # print(self._xor2add)
            # print(self._xvars)
            # self.printXlauses()
            # print("")
            doContinue = self._propagate2()
            print("c ////////////////////////////")
            print("c // Propagation no. " + str(count))
            print("c ////////////////////////////")
            doContinue |= self._propagate1()
            # doContinue = False
            # self.printClauses()
            # print("")
            # self.printClauses()
        print("c")
        if self.status:
            print("s UNSATISFIABLE")
            if self._known.useless:
                print("c Problems at variables : " + ", ".join(map(str,self._known.useless)))
        elif not self._clauses:
            for v in self._almostknown:
                self._known.addLiteral(v)
                for l in self._almostknown[v]:
                    self._known.addLiteral(l)
            print("s SATISFIABLE")
            print(self._known.dimacstr())
        else:
            print("c UNKNOWN")
            print("c Delegating to a \"real\" SAT-solver")
            print("p cnf " + str(self._nbvars) + " " + str(len(self._clauses) + len(self._known)))
            for v in self._known:
                print(str(self._known[v]) + " 0")
            for v in self._almostknown:
                for l in self._almostknown[v]:
                    print(str(v)  + " " + str(-l) + " 0")
                    print(str(-v) + " " + str(l)  + " 0")
            self.printClauses(dimacs=True)
        
            
        

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
    xolver.solve()
    # print("")
    # print("")
    # print("")
    # xolver.printClauses()
    # print("")
    # print(xolver._known)
    # print("")
    # print(xolver._almostknown)
    exit()
    

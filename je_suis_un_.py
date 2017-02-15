from pysat import *

#class je_leur_fais_des_Gauss

if __name__ == '__main__':
    banner()
    solver = Solver()
    
    if len(sys.argv) > 1:
        readFile(solver, sys.argv[1])
        solver.buildDataStructure()
    else:
        printUsage()
        sys.exit(1)

    for k in solver._clauses:
        print k
        
    #result = solver.solve(maxConflict = lambda s: int(luby(s._config.restartInc, s._restarts) * 32))
    result = solver.solve(maxConflicts = lambda s: int((100*(1.5**s._restarts))))
    if result == cst.lit_False:
        print("c UNSATISFIABLE")
    elif result == cst.lit_True:
        print("c SATISFIABLE")
    else:
        print("c UNKNOWN")
    solver.printStats()
        
    if result == cst.lit_True and solver._config.printModel: # SAT was claimed
        #print("v ", end="")
        for v in range(0, len(solver._values)):
            val = solver._values[v]
            assert val is not cst.lit_Undef
            solver._finalModel.append(val==cst.lit_True)
            if val==cst.lit_False: print("-")#, end="")
            print(str(v+1)+ " ")#, end="")
        print("")
            
    if result == cst.lit_False:
        sys.exit(20)
    if result == cst.lit_True:
        sys.exit(10)

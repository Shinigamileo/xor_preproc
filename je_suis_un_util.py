from sattypes import *

def je_suis_un_clauseCompare(c1,c2):
    len1 = c1.__len__()
    len2 = c2.__len__()
    # tri par taille
    if len1 < len2:
        return -1
    elif len1 > len2:
        return 1
    # tri par variable
    else:
        for i in range(_nbvars):
            if c1.containsLiteral(i) | c1.containsLiteral(-i):
                if not(c2.containsLiteral(i) | c2.containsLiteral(-i)):
                    return 1
            if c2.containsLiteral(i) | c2.containsLiteral(-i):
                if not(c1.containsLiteral(i) | c1.containsLiteral(-i)):
                    return -1
    return 0

def je_suis_un_trieur_de_clauses(nbVars,clauses,var=1):
    clauses_var = [[],[]]
    for c in clauses:
        clauses_var[c.containsLiteral(var) or c.containsLiteral(-var)].append(c)
    if (nbVars - var) :
        clauses_var[0] = je_suis_un_trieur_de_clauses(nbVars,clauses_var[0],var+1)
        clauses_var[1] = je_suis_un_trieur_de_clauses(nbVars,clauses_var[1],var+1)
    return clauses_var[1] + clauses_var[0]

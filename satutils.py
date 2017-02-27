import gzip, copy

from BitVector import BitVector

# Small functions to facilitate the map integers with internal values of the solver
def sign(i):
    if i > 0: return 0
    return 1

def abs(i):
    if i > 0: return i
    return -i

def myopen(f):
    if f.endswith(".gz"):
        return gzip.open(f, mode='rt')
    return open(f, 'r')

def do_all(f, l):
    for e in l: f(e)

def swap(tab,i,j):
    tab[i],tab[j] = tab[j],tab[i]

def deleteAll(tab,indexes):
    for i in sorted(indexes, reverse=True):
        del tab[i]

    
#############
# BINVECTOR #
#############

class BinEquation():
    def __init__(self, binvars=[0], result=0):
        self._vector = BitVector(bitlist=binvars)
        self.result = result

    def elements(self):
        return [i for i in range(len(self)) if self[i]]

    def __add__(self, other):
        res = BinEquation(result = self.result ^ other.result)
        res._vector = self._vector ^ other._vector
        return res

    def __str__(self):
        return str(self._vector) + "|" + str(self.result)

    def __getitem__(self, x):
        return self._vector[x]

    def __setitem__(self, x, itm):
        self._vector[x] = itm

    def __len__(self):
        return len(self._vector)

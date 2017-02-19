from heapq import *
from array import *

import gzip, copy

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
    
#
class MyArray(array):
    ''' My own array with growing function '''
    def __init__(self, *args):
        array.__init__(args)
    def growTo(self, size, fillWith=0):
        while (len(self)<size): self.append(fillWith)

class MyList(list):
    ''' My own list with growing function'''
    def __init__(self, *args):
        list.__init__(self, *args)
    def growTo(self, size, fillWith=0):
        while (len(self)<size): self.append(copy.copy(fillWith))

# Some useful classes to ease my algorithms
class VarHeap():
    _heap = [] # this is a heapq data structure
    _score = [] # score on which comparisons are made
    _entry = MyArray('i') # indexes of variables

    def __init__(self, score):
        _score = score;
        return

    def growTo(self, size):
        # don't need to do anything: I'm using heapq from python list
        return

def luby(y,x): # copied from Minisat implementation
    # Find the finite subsequence that contains index 'x', and the
    # size of that subsequence:
    # pythonic way of getting a list : [luby(2,x) for x in range(1,20)]
    size = 1; seq = 0
    while size < x + 1:
        seq += 1
        size = 2 * size + 1 

    while size-1 != x:
        size = (size-1) >> 1
        seq -= 1
        x = x % size

    return y ** seq

    
#############
# BINVECTOR #
#############

class BinEquation():
    _vector = []
    result = 0

    def __init__(self, binvars, result):
        self._vector = binvars[0:]
        self.result = result

    def elements(self):
        return [i for i in range(len(self._vector)) if self[i]]

    def __add__(self, other):
        return BinEquation([self._vector[i] ^ other._vector[i]
                            for i in range(len(self._vector))],
                           self.result ^ other.result)

    def __str__(self):
        return " ".join(list(map(lambda x:str(x),self._vector)))\
            + " | " + str(self.result)

    def __getitem__(self, x):
        return self._vector[x]

    def __setitem__(self, x, itm):
        self._vector[x] = itm

    def __len__(self):
        return len(self._vector)

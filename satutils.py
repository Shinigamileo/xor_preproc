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

def deleteAll(tab,indexes):
    for i in sorted(indexes, reverse=True):
        del tab[i]
    
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
    _intsize = 0
    _vector = []
    _nbvars = 0
    result = 0

    def __init__(self, binvars=[], result=0, intsize = 62):
        self._intsize = intsize
        self._nbvars = len(binvars)
        # And ladies and gentleman, here's the moment you craved for :...
        # THE MINUS OVER NINE THOUSAND FLOWEY TIME !!!!!
        self._vector = [int("".join(list(map(lambda e:str(e),binvars[max(i-intsize,0):i][::-1]))),2) for i in range(self._nbvars,0,-intsize) if i][::-1]
        # self._vector = binvars[0:]
        self.result = result

    def elements(self):
        return [i for i in range(len(self)) if self[i]]

    def __add__(self, other):
        res = BinEquation(result = self.result ^ other.result,
                          intsize = self._intsize)
        res._nbvars = self._nbvars
        res._vector = [self._vector[i] ^ other._vector[i]
                            for i in range(len(self._vector))]
        return res

    def __str__(self):
        filt = "{0:0"+str(self._intsize)+"b}"
        size = len(self._vector)*self._intsize
        # You loved it ? Well, prepare yourself to be amazed again :...
        # THE MINUS OVER NINE THOUSAND FLOWEY ANOTHER TIME !!!!!
        return "".join(list(map(lambda x:filt.format(x),self._vector)))[size-self._nbvars:size][::-1] + "|" + str(self.result)

    def __getitem__(self, x):
        xdiv,xmod = divmod(x,self._intsize)
        return ((self._vector[xdiv])//2**(xmod))%2

    def __setitem__(self, x, itm):
        xdiv,xmod = divmod(x,self._intsize)
        self._vector[xdiv] = (self._vector[xdiv] ^ (self._vector[xdiv] & 2**xmod)) | itm * 2**xmod

    def __len__(self):
        return self._nbvars

from matrix import *
from poly import *
from rational import *
from random import random, randint

x = polynomial(1,0);

def testcp() :
  DIM = randint(1,6);
  print(DIM);
  X = matrix.Identity(DIM,x);
  M = matrix((DIM,DIM),*tuple(random() for i in range(DIM*DIM)))
  cp = (M-X).det;
  Md = M.mapped(rational).det;
  if cp(0) != Md : print(float(Md),float(cp(0)));
  if cp(M) : print(M,cp(M));
 
for i in range(30) :
  testcp()

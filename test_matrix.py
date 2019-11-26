from matrix import *
from poly import *
from rational import *
from random import random, randint

MINDIM = 1    # min square matrix dimension for test
MAXDIM = 4    # max square matrix dimension for test
REPEATS = 10    # number of times to repeat test

x = polynomial(1,0);    # the polynomial x

def testcp(dim,verbose=False) :    # characteristic polynomial test
  X = matrix.Identity(dim,x);
  M = matrix(dim,dim,
             tuple(xrational(random(),random()) for i in range(dim*dim)))
  cp = (M-X).det;
  try :
    if cp.denominator != 1 :
      print('Charpoly not a polynomial? Denominator = %s'
            %(cp.denominator.mapcoeffs(complex)));
      verbose=True;
    cp = cp.numerator;
  except :
    pass;    # was already polynomial
  Md = M.det;
  if verbose or cp(0) != Md or cp(M) :
    print(M.mapped(complex));
    print(cp.mapcoeffs(complex));
  if cp(0) != Md : # check that characteristic polynomial at 0 is determinant
    print('det %s != charpoly(0) %s'%(float(Md),float(cp(0))));
  cpM = cp(M);
  if cp(M) :    # check that matrix satisfies its characteristic polynomial
    print(M,cpM);
  MT = M.T
  cpMT = cp(MT);
  if cpMT :    # check that transposed matrix satisfies characteristic polynomial
    print(MT,cpMT);

def testinv(dim,verbose=False) :    # matrix inverse test
  I = matrix.Identity(dim);
  M = matrix(dim,dim,tuple(xrational(random(),random()) for i in range(dim*dim)));
  if M.det :
    if M.inverse*M != I or M*M.inverse != I :
      print('matrix inverse failed for');
      print(M);
  M = matrix(dim,dim,tuple(qrational(random(),random(),random(),random()) for i in range(dim*dim)));
  if M.rank == dim :
    if M.inverse*M != I or M*M.inverse != I :
      print('matrix inverse failed for');
      print(M);
    

if __name__=='__main__' :
  for i in range(REPEATS) :
    dim = randint(MINDIM,MAXDIM);
    print(dim);
    testcp(dim);
    testinv(dim);

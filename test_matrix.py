from matrix import *
from poly import *
from rational import *
from random import random, randint, randrange

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
  except Exception :
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
    
def testattr(dim,verbose=False) :    # matrix attribute test
  I = matrix.Identity(dim);
  if I.dims != (dim,dim) :
    print('matrix.dims failed for Identity(%d)'%(dim));
  if I.squeeze != I :
    print('matrix.squeeze failed for Identity(%d)'%(dim));
  if I.det != 1 :
    print('matrix.det failed for Identity(%d)'%(dim));
  if I.determinant != 1 :
    print('matrix.determinant failed for Identity(%d)'%(dim));
  if I.tr != dim :
    print('matrix.tr failed for Identity(%d)'%(dim));
  if I.trace != dim :
    print('matrix.trace failed for Identity(%d)'%(dim));
  if I.rank != dim :
    print('matrix.rank failed for Identity(%d)'%(dim));
  if I.inverse != I :
    print('matrix.inverse failed for Identity(%d)'%(dim));
  if I.conjugate != I :
    print('matrix.conjugate failed for Identity(%d)'%(dim));
  if I.T != I :
    print('matrix.T failed for Identity(%d)'%(dim));
  if I.transpose != I :
    print('matrix.transpose failed for Identity(%d)'%(dim));
  if I.H != I :
    print('matrix.I failed for Identity(%d)'%(dim));
  if I.conjugate_transpose != I :
    print('matrix.conjugate_transpose failed for Identity(%d)'%(dim));
  I = bmatrix.Identity(dim);
  if I.dims != (dim,dim) :
    print('bmatrix.dims failed for Identity(%d)'%(dim));
  if I.squeeze != I :
    print('bmatrix.squeeze failed for Identity(%d)'%(dim));
  if I.det != 1 :
    print('bmatrix.det failed for Identity(%d)'%(dim));
  if I.determinant != 1 :
    print('bmatrix.determinant failed for Identity(%d)'%(dim));
  if I.tr != dim&1 :
    print('bmatrix.tr failed for Identity(%d)'%(dim));
  if I.trace != dim&1 :
    print('bmatrix.trace failed for Identity(%d)'%(dim));
  if I.rank != dim :
    print('bmatrix.rank failed for Identity(%d)'%(dim));
  if I.inverse != I :
    print('bmatrix.inverse failed for Identity(%d)'%(dim));
  if I.conjugate != I :
    print('bmatrix.conjugate failed for Identity(%d)'%(dim));
  if I.T != I :
    print('bmatrix.T failed for Identity(%d)'%(dim));
  if I.transpose != I :
    print('bmatrix.transpose failed for Identity(%d)'%(dim));
  if I.H != I :
    print('bmatrix.I failed for Identity(%d)'%(dim));
  if I.conjugate_transpose != I :
    print('bmatrix.conjugate_transpose failed for Identity(%d)'%(dim));

def ceq(c,*v) :
  if not eval(c) : print(c,v);

def testb(dim) :
  # bmatrix tests
  M0,M1,M2 = (bmatrix((dim,dim),randrange(dim*dim)) for _ in range(3));
  ceq('v[0] == -v[0]',M0);
  ceq('v[0]*v[0].Identity(v[0].dims[1]) == v[0]',M0);
  ceq('v[0].Identity(v[0].dims[0])*v[0] == v[0]',M0);
  if M0.rank == dim :
    ceq('v[0]*v[0]**-1 == v[0].Identity(v[0].dims[0])',M0);
    ceq('v[0]**-1*v[0] == v[0].Identity(v[0].dims[0])',M0);
    ceq('v[0].det == 1',M0);
  else :
    ceq('v[0].det == 0',M0);
  ceq('v[0]+v[1] == v[0]-v[1]',M0,M1);
  ceq('(v[0]+v[1]).tr == (v[0].tr+v[1].tr)%2',M0,M1);
  testtr(M0,M1,M2);

def testm(dim) :
  # simple matrix tests
  M0,M1,M2 = (matrix(dim,dim,
                    tuple(xrational(random(),random()) for i in range(dim*dim)))
              for _ in range(3));
  ceq('(v[0]+v[1]).tr == v[0].tr+v[1].tr',M0,M1);
  testtr(M0,M1,M2);

def testtr(M0,M1,M2) :
  ceq('v[0]+v[1] == v[1]+v[0]',M0,M1);
  ceq('v[0]-v[1]+v[1] == v[0]',M0,M1);
  ceq('v[0]-v[1] == -(v[1]-v[0])',M0,M1);
  ceq('(v[0]*v[1]).T == v[1].T*v[0].T',M0,M1);
  ceq('(v[0]*v[1])*v[2] == v[0]*(v[1]*v[2])',M0,M1,M2);
  ceq('(v[0]+v[1])*v[2] == v[0]*v[2]+v[1]*v[2]',M0,M1,M2);
  ceq('v[0]*(v[1]+v[2]) == v[0]*v[1]+v[0]*v[2]',M0,M1,M2);
  ceq('v[0].tr == v[0].T.tr',M0);
  ceq('(v[0]*v[1]).tr == (v[1]*v[0]).tr',M0,M1);
  ceq('(v[0]*v[1]*v[2]).tr == (v[1]*v[2]*v[0]).tr == (v[2]*v[0]*v[1]).tr',M0,M1,M2)
  ceq('v[0]**3 == v[0]*v[0]*v[0]',M0);

if __name__=='__main__' :
  for i in range(REPEATS) :
    dim = randint(MINDIM,MAXDIM);
    print(dim);
    testattr(dim);
    testm(dim);
    testb(dim);
    testcp(dim);
    testinv(dim);

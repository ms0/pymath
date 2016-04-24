from random import randrange, sample

from ffield import *
from matrix import *

MAXCHAR = 64;    # limit on characteristics to test
LIMIT2 = 128;    # limit on ff size for full pair testing
LIMIT3 = 64;     # limit on ff size for full triple testing
LIMITM = 16;     # limit on size of vandermonde matrix

def ceq(c,*v) :
  z = type(v[0])(0);
  o = type(v[0])(1);
  if not eval(c) : print(c,v);

def cvs(g) :
  return ''.join(map(lambda x: zits[x],unpack(g.p,g.x)));

def find_irr(p,n) :
  if n <= 1 : return 0;
  while True :
    x = randrange(p**n);
    tupoly = unpack(p,x);
    if isirreducible((n-len(tupoly))*(0,)+tupoly,p) : return x;

generator=None;

def randfield(p,n) :
  return ffield(p,n,find_irr(p,n));

def test(p,n) :
  global generator
  g = randfield(p,n);
  print(g);
  pn = p**n;
  z = g(0);
  o = g(1);
  ceq('not o+-1',o);
  ceq('not -1+o',o);
  ceq('not o-1',o);
  ceq('not z-0',z);
  ceq('not 1-o',o);
  ceq('not 0-z',z);
  generator = None;
  for i in xrange(pn) :
    test1(g,i);
  if pn > LIMIT3 :
    for i in xrange(LIMIT3) :
      for j in xrange(LIMIT3) :
        for k in xrange(LIMIT3) :
          test3(g,randrange(pn),randrange(pn),randrange(pn));
  mtest(g);

def mtest(g) :    # matrix tests
  p = g.p;
  n = g.n;
  pn = p**n;
  z = g(0);
  o = g(1);
  while True :    # find an invertible matrix and verify inverse works
    M = matrix((3,3),tuple(g(randrange(pn)) for i in range(9)));
    if M.det :
      ceq('1/v[1]*v[1]==Identity(3,o)==v[1]*v[1].inverse',z,M);
      break;
  d = min(pn-1,LIMITM);    # check Vandermonde matrix determinant
  M = Identity(d,z);
  p = o;
  for i,a in enumerate(sample(xrange(1,pn),d)) :
    a = g(a);
    for j in range(i) :
      p *= a-M[j,1];
    for j in range(d) :
      M[i,j] = a**j;
  ceq('v[0]==v[1].det',p,M);


def test1(g,i) :
  global generator
  p = g.p;
  n = g.n;
  pn = p**n;
  gi = g(i);
  if not generator and isgenerator(gi) :
    generator = gi;
    print('  generator %s'%(str(gi)));
  ceq('type(v[0])(unpack(v[0].p,v[0].x))==v[0]==type(v[0])(v[0].x)',gi);
  if p < 16 : ceq('type(v[0])(cvs(v[0]))==v[0]',gi);
  ceq('not v[0]+-v[0]',gi);
  ceq('v[0]*z==z==z*v[0]',gi);
  ceq('v[0]*0==z==0*v[0]',gi);
  ceq('v[0]*o==v[0]==o*v[0]',gi);
  ceq('v[0]*1==v[0]==1*v[0]',gi);
  ceq('v[0]-v[0]==z',gi);
  ceq('0-v[0]==-v[0]',gi);
  ceq('v[0]+1==1+v[0]',gi);
  ceq('v[0]+1-1==v[0]',gi);
  ceq('1+v[0]-1==v[0]',gi);
  ceq('1-v[0]-1==-v[0]',gi);
  if gi :
    ceq('v[0]/v[0]==o',gi);
    ceq('1/v[0]*v[0]==o',gi);
    ceq('1/v[0]==v[0]**-1',gi);
    ceq('o==v[0]**0',gi);
  if p > 2 :
    ceq('v[0]*2-v[0]==v[0]',gi);
    ceq('2*v[0]-v[0]==v[0]',gi);
    ceq('v[0]/2*2==v[0]',gi);
    if gi : ceq('2/v[0]/2==1/v[0]',gi);
  ceq('v[0]==v[0]**1',gi);
  ceq('v[0]*v[0]==v[0]**2',gi);
  for j in xrange(7) :
    for k in xrange(7) :
      ceq('v[0]**(v[1]+v[2])==v[0]**v[1]*v[0]**v[2]',gi,j,k)
      ceq('v[0]**(v[1]*v[2])==(v[0]**v[1])**v[2]',gi,j,k)
  if pn <= LIMIT2 :
    for j in xrange(pn) :
      test2(g,i,j);
      if pn <= LIMIT3 :
        for k in xrange(pn) :
          test3(g,i,j,k);
  else :
    for j in xrange(LIMIT2) :
      test2(g,i,randrange(pn));

def test2(g,i,j) :    # pair testing
  gi = g(i);
  gj = g(j);
  ceq('v[0]+v[1]==v[1]+v[0]',gi,gj);
  ceq('v[0]*v[1]==v[1]*v[0]',gi,gj);
  ceq('v[0]+v[1]-v[0]==v[1]',gi,gj);
  ceq('v[0]-v[1]+v[1]==v[0]',gi,gj);
  if gj :
    ceq('v[0]/v[1]*v[1]==v[0]',gi,gj);
    ceq('v[0]*v[1]/v[1]==v[0]',gi,gj);
  for k in xrange(7) :
    ceq('(v[0]*v[1])**v[2]==v[0]**v[2]*v[1]**v[2]',gi,gj,k);

def test3(g,i,j,k) :    # triple testing
  gi = g(i);
  gj = g(j);
  gk = g(k);
  ceq('(v[0]+v[1])+v[2]==v[0]+(v[1]+v[2])',gi,gj,gk);
  ceq('(v[0]*v[1])*v[2]==v[0]*(v[1]*v[2])',gi,gj,gk);
  ceq('v[0]*(v[1]+v[2])==v[0]*v[1]+v[0]*v[2]',gi,gj,gk);

def isgenerator(x) :
  # order of the group is p**n-1, and its cyclic
  # if x is a generator, then x**e will be a generator for e prime to p**n-1
  # so there are phi(p**n-1) generators
  # p     n=1    n=2    n=3    n=4    n=5      table of p**n-1
  # 2      1      3      7      15     31
  #          1      2      6      8      30
  # 3      2      8      26     80    242
  #          1      4     12     32     110
  # 5      4     24     124    624   3124
  #          2      8     60    192    1400
  # 7      6     48     342   2400  16806
  #          2     16    108    640    5600
  # if x is not a generator, then for one of the prime factors qi of p**n-1,
  #   x**((p**n-1)/qi) will be 1
  if not x: return False;
  p = x.p;
  n = x.n;
  o = p**n-1;
  for q in factors(o) :
    if not x**(o//q)-1 : return False;
  return True;

if __name__=='__main__' :
  for p in xrange(MAXCHAR) :
    if isprime(p) :
      test(p,1);
      test(p,2);
      test(p,3);

# NOTE: we should test whether gcd is faster than exp for computing inverse

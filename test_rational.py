# NOTE: this includes a test for rational.__pow__ as used in sha2.py
# NOTE: test_matrix.py also tests rational.py functionality
# NOTE: test_poly.py also tests rational.py functionality

import sys

if sys.version_info[0] < 3 :

  def isint(x) :
    """Return True iff an integer"""
    return isinstance(x,(int,long));

else :

  def isint(x) :
    """Return True iff an integer"""
    return isinstance(x,int);

  xrange = range;

from random import Random
from rational import *
from timeit import timeit, default_timer

try :
  from timer import process_time
except Exception :
  process_time = default_timer;

R=Random();
randint=R.randint;
def random() :
  """Return a random rational uniformly distributed in [0,1]"""
  s = set_significance();
  h = (s+1)//2;
  while True :
    a = R.getrandbits(h);
    if a : break;
  b = R.getrandbits(h);
  if a > b: a,b=b,a;
  return rational(a,b);

R.seed(0);    # for test reproducibility

def timing(name,stmt,repeats=16,nargs=1,plex=0) :
  """Print time taken by stmt with nargs random real or complex args"""
  t = timeit(
    stmt=stmt if not '[i]' in stmt else
    'for i in %s(0,%d,%d):%s'%(xrange.__name__,repeats*nargs,nargs,stmt),
    setup='from rational import rational,xrational,qrational,set_significance,exp,sin,cos,tan,log,asin,acos,atan,atan2,sinh,cosh,tanh,asinh,acosh,atanh,erf,erfc,gamma,lgamma,fsum\nfrom test_rational import random\nr=[qrational(2*random()-1,2*random()-1,2*random()-1,2*random()-1) if %d > 1 else xrational(2*random()-1,2*random()-1) if %d else 2*random()-1 for _ in %s(%d)]\nu=[(1+x.real)/2 for x in r]'%(plex,plex,xrange.__name__,repeats*nargs),
    timer=process_time,number=1);
  print('%s\t%f'%(name,t/repeats));

def ceq(c,v=()) :
  """Evaluate expression c using tuple of values v; print if nonzero"""
  if not eval(c) : print(c,v);

def roottest(numbers=None,roots=(2,3),nbits=(32,64)) :
  """Test calculation of square and cube roots used in sha.py"""
  if not numbers :
    from sha2 import P
    numbers = P;
  iroot = lambda x,r,b: int(rational(x<<(r*b))**rational(1,r));
  ipow = lambda x,r,b: (x**r)>>(r*b);
  for n in numbers :
    for r in roots :
      for b in nbits :
        x = iroot(n,r,b);
        xr = ipow(x,r,b);
        if xr != n :
          if xr >= n :
            print('%d root of %d overestimated for nbits=%d'%(r,n,b));
            break;
          if ipow(x+1,r,b) != n :
            print('%d root of %d underestimated for nbits=%d'%(r,n,b));
            break;

def testops(v) :    # v is vector of 3 values to be tested
  """Test operators using 3-vector of values"""
  testops1(v);
  testops2(v);
  testops3(v);

def testo23(v) :
  testops2(v);
  testops3(v);

def testops1(v) :
  ceq('v[0]-v[0] == 0',v[:1])
  ceq('v[0]+-v[0] == 0',v[:1])
  ceq('not v[0] or v[0]/v[0] == 1',v[:1])
  ceq('not v[0] or v[0]*v[0]**-1 == 1',v[:1])
  ceq('not v[0] or 1/v[0] == v[0]**-1',v[:1])
  ceq('0*v[0] == 0',v[:1])
  ceq('1*v[0] == v[0]',v[:1])
  ceq('-1*v[0] == -v[0]',v[:1])
  if isinstance(v[0],(xrational,qrational)) :
    ceq('not v[0] or abs(((v[0]*~v[0])-abs(v[0])**2)/(v[0]*~v[0]))<<set_significance() < 1',v[:1])

def testops2(v) :
  ceq('v[0]+v[1] == v[1]+v[0]',v[:2])
  if not (isinstance(v[0],qrational) or isinstance(v[1],qrational))  :
    ceq('v[0]*v[1] == v[1]*v[0]',v[:2])
  ceq('not v[1] or v[0]/v[1]*v[1] == v[0]',v[:2])
  ceq('v[0]-v[1]+v[1] == v[0]',v[:2])
  ceq('type(v[0])==type(v[1]) and v[0]==v[0]',(v[0],eval(repr(v[0]))));
  if v[1] :
    ceq('v[0]//v[1]*v[1]+v[0]%v[1]==v[0]',v[:2]);
    ceq('v[0]//v[1]==(v[0]//v[1]).hurwitz()',v[:2]);
    ceq('(v[0]%v[1]).abs2() < v[1].abs2()',v[:2]);
    ceq('divmod(v[0],v[1])==(v[0]//v[1],v[0]%v[1])',v[:2]);
  # remainder of tests require integers of some kind
  v = (v[0].hurwitz(),v[1].hurwitz());
  ceq('xgcd(v[0],v[1])[0] == xgcd(v[0],v[1])[1]*v[0]+xgcd(v[0],v[1])[2]*v[1]',v[:2]);
  if v[0] or v[1] :
    ceq('not v[0]%xgcd(v[0],v[1])[0] and not v[1]%xgcd(v[0],v[1])[0]',v[:2]);

def testops3(v) :
  ceq('(v[0]+v[1])+v[2] == v[0]+(v[1]+v[2])',v)
  ceq('(v[0]*v[1])*v[2] == v[0]*(v[1]*v[2])',v)
  ceq('v[0]*(v[1]+v[2]) == v[0]*v[1]+v[0]*v[2]',v)
  ceq('(v[0]+v[1])*v[2] == v[0]*v[2]+v[1]*v[2]',v)

def ratspectest() :
  """Test operations on nan and signed zeroes and infinities"""
  p0 = rational();
  m0 = -p0;
  pinf = rational(1,0);
  minf = -pinf;
  nan = rational(0,0);
  half = rational(1,2);
  ceq('v[0]!=v[0]',(nan,));
  ceq('v[0] is v[1]',(nan,eval(repr(nan))));
  for x in (p0,m0,pinf,minf) :
    ceq('v[0]==v[0]',(x,));
    ceq('v[0]==v[1]',(x,eval(repr(x))));
  ceq('v[0]==v[1]',(p0,m0));         # +0 == -0
  ceq('v[0]!=v[1]',(pinf,minf));     # +inf != -inf
  ceq('v[0]>v[1]',(pinf,minf));      # +inf > -inf
  ceq('v[0]>1>v[1]',(pinf,minf));    # +inf > 1 > -inf
  ceq('v[0]>v[2]>v[1]',(pinf,minf,p0));    # +inf > +0 > -inf
  ceq('v[0]>v[2]>v[1]',(pinf,minf,m0));    # +inf > -0 > -inf
  ceq('v[0]>v[2]>=v[3]>v[1]',(pinf,minf,p0,m0));    # +inf > +0 >= -0 > -inf
  ceq('v[0]>v[3]>=v[2]>v[1]',(pinf,minf,p0,m0));    # +inf > -0 >= +0 > -inf
  ceq('v[1]<v[0]',(pinf,minf));      # -inf < +inf
  ceq('v[1]<1<v[0]',(pinf,minf));    # -inf < 1 < +inf
  ceq('v[1]<v[2]<v[0]',(pinf,minf,p0));    # -inf < +0 < +inf
  ceq('v[1]<v[2]<v[0]',(pinf,minf,m0));    # -inf < -0 < +inf
  ceq('v[0]>v[2]>=v[3]>v[1]',(pinf,minf,p0,m0));    # +inf > +0 >= -0 > -inf
  ceq('v[0]>v[3]>=v[2]>v[1]',(pinf,minf,p0,m0));    # +inf > -0 >= +0 > -inf
  ceq('v[1]<v[2]<=v[3]<v[0]',(pinf,minf,p0,m0));    # -inf < +0 <= -0 > +inf
  ceq('v[1]<v[3]<=v[2]<v[0]',(pinf,minf,p0,m0));    # -inf < -0 <= +0 > +inf
  ceq('v[0] is 1/v[1]',(p0,pinf));   # +0 is 1/+inf
  ceq('v[0] is 1/v[1]',(m0,minf));   # -0 is 1/-inf
  ceq('v[0] is -1/v[1]',(p0,minf));  # +0 is -1/-inf
  ceq('v[0] is -1/v[1]',(m0,pinf));  # -0 is -1/+inf
  ceq('v[1] is 1/v[0]',(p0,pinf));   # +inf is 1/+0
  ceq('v[1] is 1/v[0]',(m0,minf));   # -inf is 1/-0
  ceq('v[1] is -1/v[0]',(p0,minf));  # -inf is -1/+0
  ceq('v[1] is -1/v[0]',(m0,pinf));  # +inf is -1/-0
  ceq('v[0] is v[0]/v[1]',(p0,pinf));# +0 is +0/+inf
  ceq('v[0] is v[0]/v[1]',(m0,pinf));# -0 is -0/+inf
  ceq('-v[0] is v[0]/v[1]',(p0,minf)); # -+0 is +0/-inf
  ceq('-v[0] is v[0]/v[1]',(m0,minf)); # --0 is -0/-inf
  ceq('v[1] is v[1]/v[0]',(p0,pinf));# +inf is +inf/+0
  ceq('v[1] is v[1]/v[0]',(p0,minf));# -inf is -inf/+0
  ceq('-v[1] is v[1]/v[0]',(m0,pinf)); # -+inf is -0/+inf
  ceq('-v[1] is v[1]/v[0]',(m0,minf)); # --inf is -0/-inf
  ceq('v[0] is not v[1]',(p0,m0));   # +0 is not -0
  ceq('v[0] is v[0]+v[0]',(p0,));    # +0 is +0 + +0
  ceq('v[0] is v[0]+v[0]',(m0,));    # -0 is -0 + -0
  ceq('v[0] is v[1]+v[0]',(p0,m0));  # +0 is -0 + +0
  ceq('v[0] is v[0]-v[0]',(p0,));    # +0 is +0 - +0
  ceq('v[0] is v[0]-v[1]',(p0,m0));  # +0 is +0 - -0
  ceq('v[0] is v[1]-v[1]',(p0,m0));  # +0 is -0 - -0
  ceq('v[1] is v[1]-v[0]',(p0,m0));  # -0 is -0 - +0
  ceq('v[0] is v[0]*v[0]',(p0,));    # +0 is +0 * +0
  ceq('v[0] is v[1]*v[1]',(p0,m0));  # +0 is -0 * -0
  ceq('v[1] is v[0]*v[1]',(p0,m0));  # -0 is +0 * -0
  ceq('v[1] is v[1]*v[0]',(p0,m0));  # -0 is -0 * +0
  ceq('v[0] is v[0]**v[1]',(p0,half));  # +0 is (+0)**.5
  ceq('v[0] is v[0]**v[1]',(m0,half));  # -0 is (-0)**.5
  ceq('v[0] is v[0]**v[1]',(p0,1));  # +0 is (+0)**1
  ceq('v[0] is v[0]**v[1]',(m0,1));  # -0 is (-0)**1
  ceq('v[0]**0 == 1',(p0,));         # (+0)**0 == 1
  ceq('v[0]**0 == 1',(m0,));         # (-0)**0 == 1    
  ceq('v[0]<<1 is v[0]',(p0,));      # (+0)<<1 == +0
  ceq('v[0]<<1 is v[0]',(m0,));      # (-0)<<1 == -0
  ceq('v[0]>>1 is v[0]',(p0,));      # (+0)>>1 == +0
  ceq('v[0]>>1 is v[0]',(m0,));      # (-0)>>1 == -0
  ceq('v[0] is -v[1]',(p0,m0));      # +0 is --0
  ceq('v[1] is -v[0]',(p0,m0));      # -0 is -+0
  ceq('v[0] is abs(v[0])',(p0,));    # +0 is abs(+0)
  ceq('v[0] is abs(v[1])',(p0,m0));  # +0 is abs(-0)
  ceq('v[0] is -v[1]',(pinf,minf));  # +inf is --inf
  ceq('v[1] is -v[0]',(pinf,minf));  # -inf is -+inf
  ceq('v[0] is abs(v[0])',(pinf,));    # +inf is abs(+inf)
  ceq('v[0] is abs(v[1])',(pinf,minf));  # +inf is abs(-inf)
  ceq('v[0] is v[1]/v[1]',(nan,p0));  # nan is +0/+0
  ceq('v[0] is v[1]/v[1]',(nan,m0));  # nan is -0/-0
  ceq('v[0] is v[1]/v[2]',(nan,p0,m0));  # nan is +0/-0
  ceq('v[0] is v[2]/v[1]',(nan,p0,m0));  # nan is -0/+0
  ceq('v[0] is v[1]/v[1]',(nan,pinf));  # nan is +inf/+inf
  ceq('v[0] is v[1]/v[1]',(nan,minf));  # nan is -inf/-inf
  ceq('v[0] is v[1]/v[2]',(nan,pinf,minf));  # nan is +inf/-inf
  ceq('v[0] is v[2]/v[1]',(nan,pinf,minf));  # nan is -inf/+inf
  ceq('v[0] is v[1]*v[2]',(nan,p0,pinf));  # nan is +0*+inf
  ceq('v[0] is v[2]*v[1]',(nan,p0,pinf));  # nan is +inf*+0
  ceq('v[0] is v[1]*v[2]',(nan,m0,minf));  # nan is -0*-inf
  ceq('v[0] is v[2]*v[1]',(nan,m0,minf));  # nan is -inf*-0
  ceq('v[0] is v[1]+v[2]',(nan,pinf,minf));  # nan is +inf+-inf  
  ceq('v[0] is v[2]+v[1]',(nan,pinf,minf));  # nan is -inf++inf
  ceq('v[0] == v[0]+v[1]',(1,p0));   # 1 == 1++0
  ceq('v[0] == v[0]+v[1]',(1,m0));   # 1 == 1+-0
  ceq('v[0] == v[0]+v[1]',(pinf,1)); # +inf == +inf+1
  ceq('v[0] == v[0]+v[1]',(minf,1)); # -inf == -inf+1
  ceq('v[0] == v[0]*v[1]',(pinf,2)); # +inf == +inf*2
  ceq('v[0] == v[0]*v[1]',(minf,2)); # -inf == -inf*2
  ceq('v[0] == v[1]*v[2]',(pinf,minf,-2));  # +inf == -inf*-2
  ceq('v[1] == v[0]*v[2]',(pinf,minf,-2));  # -inf == +inf*-2
  for x in (69,p0,m0,pinf,minf,nan) :
    ceq('v[0] != v[1]',(nan,x));
    ceq('v[1] != v[0]',(nan,x));
    ceq('not v[0] < v[1]',(nan,x));
    ceq('not v[1] < v[0]',(nan,x));
    ceq('not v[0] <= v[1]',(nan,x));
    ceq('not v[1] <= v[0]',(nan,x));
    ceq('not v[0] == v[1]',(nan,x));
    ceq('not v[1] == v[0]',(nan,x));
    ceq('not v[0] >= v[1]',(nan,x));
    ceq('not v[1] >= v[0]',(nan,x));
    ceq('not v[0] > v[1]',(nan,x));
    ceq('not v[1] > v[0]',(nan,x));
    ceq('v[0] is v[0]+v[1]',(nan,x));
    ceq('v[0] is v[0]-v[1]',(nan,x));
    ceq('v[0] is v[0]*v[1]',(nan,x));
    ceq('v[0] is v[0]/v[1]',(nan,x));
    ceq('v[0] is v[1]+v[0]',(nan,x));
    ceq('v[0] is v[1]-v[0]',(nan,x));
    ceq('v[0] is v[1]*v[0]',(nan,x));
    ceq('v[0] is v[1]/v[0]',(nan,x));

def rattest(repeats=1000,nrange=(-100,100),drange=(1,100)) :
  """Test rational operators"""
  ratspectest()
  for i in xrange(repeats) :
    testops(tuple(rational(randint(*nrange),randint(*drange)) for j in xrange(3)));
  
def xtest(repeats=1000,nrange=(-100,100),drange=(1,100)) :
  """Test xrational operators"""
  for i in xrange(repeats) :
    testops(tuple(xrational(rational(randint(*nrange),randint(*drange)),
                            rational(randint(*nrange),randint(*drange))) for j in xrange(3)));

def qtest(repeats=1000,nrange=(-100,100),drange=(1,100)) :
  """Test qrational operators"""
  for i in xrange(repeats) :
    testops(tuple(qrational(rational(randint(*nrange),randint(*drange)),
                            rational(randint(*nrange),randint(*drange)),
                            rational(randint(*nrange),randint(*drange)),
                            rational(randint(*nrange),randint(*drange))) for j in xrange(3)));

def vtest(repeats=1000,nrange=(-100,100),drange=(1,100)) :
  """Test vector operators"""
  for i in xrange(repeats) :
    v = tuple(qrational(0,
                        rational(randint(*nrange),randint(*drange)),
                        rational(randint(*nrange),randint(*drange)),
                        rational(randint(*nrange),randint(*drange))) for j in xrange(2));
    ceq('v[0].cross(v[1])==qrational(0,*(v[0]*v[1]).vector)',v[:2]);
    ceq('v[0].dot(v[1])==-(v[0]*v[1]).real',v[:2]);

def mixtest(repeats=1000,nrange=(-100,100),drange=(1,100)) :
  """Text mixed arguments"""
  for i in xrange(repeats) :
    t = tuple(randint(0,2) for j in xrange(3));
    testo23(tuple(rational(randint(*nrange),randint(*drange)) if t[j] == 0 else
                  xrational(rational(randint(*nrange),randint(*drange)),
                            rational(randint(*nrange),randint(*drange))) if t[j] == 1 else
                  qrational(rational(randint(*nrange),randint(*drange)),
                            rational(randint(*nrange),randint(*drange)),
                            rational(randint(*nrange),randint(*drange)),
                            rational(randint(*nrange),randint(*drange))) for j in xrange(3)));

def sigbits(computed,actual=1) :
  """Return number of significant bits of computed relative to actual"""
  if not actual :
    return 0 if computed != actual else inf;
  return -abs(1-computed/actual).log(2);

def approximatebits(x,a,r) :
  """Return 9-character string showing actual number of signficant bits
in x.approximate(1<<a) compared to hi-precision reference value r"""
  xa = sigbits(x.approximate(1<<a),r);
  return '%9.2f'%(xa) if isfinite(xa) else ' '*9;

# higher-precision reference values for constants defined in rational.py
_e = rational(chain((2,1),chain.from_iterable((2*i,1,1) for i in xrange(1,40))));
_log2e = rational((1,2,3,1,6,3,1,1,2,1,1,1,1,3,10,1,1,1,2,1,1,1,1,3,2,3,1,13,7,4,1,1,1,7,2,4,1,1,2,5,14,1,10,1,4,2,18,3,1,4,1,6,2,7,3,3,1,13,3,1,4,4,1,3,1,1,1,1,2,17,3,1,2,32,1,1,1,1,3,1,4,5,1,1,4,1,3,9,8,1,1,7,1,1,1,1,1,1,1,4,5,4,32,1,19,2,1,1,52,43,1,1,7,2,1,3,28));
_pi = rational((3,7,15,1,292,1,1,1,2,1,3,1,14,2,1,1,2,2,2,2,1,84,2,1,1,15,3,13,1,4,2,6,6,99,1,2,2,6,3,5,1,1,6,8,1,7,1,2,3,7,1,2,1,1,12,1,1,1,3,1,1,8,1,1,2,1,6,1,1,5,2,2,3,1,2,4,4,16,1,161,45,1,22,1,2,2,1,4,1,2,24,1,2,1,3,1,2,1,1));
_rootpi = rational((1,1,3,2,1,1,6,1,28,13,1,1,2,18,1,1,1,83,1,4,1,2,4,1,288,1,90,1,12,1,1,7,1,3,1,6,1,2,71,9,3,1,5,36,1,2,2,1,1,1,2,5,9,8,1,7,1,2,2,1,63,1,4,3,1,6,1,1,1,5,1,9,2,5,4,1,2,1,1,2,20,1,1,2,1,10,5,2,1,100,11,1,9,1,2,1,1,1,1));
_eulerconstant = rational((0,1,1,2,1,2,1,4,3,13,5,1,1,8,1,2,4,1,1,40,1,11,3,7,1,7,1,1,5,1,49,4,1,65,1,4,7,11,1,399,2,1,3,2,1,2,1,5,3,2,1,10,1,1,1,1,2,1,1,3,1,4,1,1,2,5,1,3,6,2,1,2,1,1,1,2,1,3,16,8,1,1,2,16,6,1,2,2,1,7,2,1,1,1,3,1,2,1,2,13,5,1,1,1,6,1,2,1,1,11,2,5,6));
_goldenratio = rational(1 for i in xrange(250));  # (1+root5)/2
_root2 = rational(min(i,2) for i in xrange(1,151));

def atest() :    # test approximate
  """Test approximate()"""
  # verify that relative difference is within requested accuracy
  print('bits requested    e       pi     rootpi    log2e    root2  goldenratio');
  for a in range(0,321,32) :
    print('%7d     %s%s%s%s%s%s'%(a,
                                approximatebits(e,a,_e),
                                approximatebits(pi,a,_pi),
                                approximatebits(rootpi,a,_rootpi),
                                approximatebits(log2e,a,_log2e),
                                approximatebits(root2,a,_root2),
                                approximatebits(goldenratio,a,_goldenratio)));

half=rational(1,2);
zero=rational(0);
one=rational(1);

def ttest(significance,header=True) :
  """Test accuracy of exp and log for real and complex values"""
  set_significance(significance);
  # try values at maximum of series range:
  # exp: (imaginary arg tests sin and cos) [0,1/2]
  # ln: (v2/2,1)
  # arg (atan):  [0,v2-1]
  # sin: [-pi/27,pi/27]
  # __pow__ tests all of the above
  ceq('rational(0).exp()==1');
  ceq('rational(1).log()==0');
  ceq('rational(2).log(2)==1');
  ceq('xrational(1).arg()==0');
  ceq('xrational(0,1).arg()==hpi');
  ceq('xrational(-1,0).arg()==pi');
  ceq('xrational(1,1).arg()==qpi');
  if header :
    print('sig      exp(.5)**2            exp(i)**tau    exp(log(x))   exp(i*arg(1+ix)');
    print(' | (3**.5)**2|  exp(i*tau/3)**3     |   log(exp(x))| arg(exp(ix)   |');
#         'ddd   d.dd  d.dd  (d.dd,d.dd)  (d.dd,d.dd)  d.dd  d.dd  d.dd  (d.dd,d.dd)'   
  # tests of exp, ln, sin, atan ...
  # exp(ln x) = x, ln(exp(x)) = x
  # exp(ix) = cos(x) + i sin(x)
  # arg(x+iy) = atan(y/x)
  # i.e., (i*x).exp().arg() = x and abs((i*x).exp()) = 1
  i = xrational(0,1);
  l2ri = lambda c:(-abs(c.real).log(2),-abs(c.imag).log(2));
  r = [];
  r.append(sigbits((3**half)**2,3));
  r.append(sigbits(half.exp()**2,e));
  r.append(l2ri(1-(i*tau/3).exp()**3));
  r.append(l2ri(1-i.exp()**tau));
  bits = inf;    #  log(exp(x)) ~ x
  for n in xrange(16) :
    x = rational(n+1,32);
    bits = min(bits,sigbits(x.exp().log(),x));
  r.append(bits);
  bits = inf;    # exp(log(x)) ~ x
  for n in xrange(16) :
    x = (1-roothalf)*(n+1)/16;
    bits = min(bits,sigbits(x.log().exp(),x));
  r.append(bits);
  bits = inf;
  for n in xrange(1,11) :    # arg(exp(ix) ~ x
    x = rational(n,11)*hpi;
    bits = min(bits,sigbits((i*x).exp().arg(),x));
  r.append(bits);
  bits = inf;    # exp(i*arg(1+ix)): imag/real ~ x
  mbits = inf;   # exp(i*arg(1+ix)): imag**2+real**2 = 1
  for n in xrange(8) :
    x = rational(n+1,8)*froot2;
    z = ((1+i*x).arg()*i).exp();
    bits = min(bits,sigbits(z.imag/z.real,x));
    mbits = min(mbits,sigbits(z*~z));
  r.append((mbits,bits));
  def b(x) :
    try :
      x = iter(x);
      return '(%s)'%(','.join(b(i) for i in x));
    except Exception :
      return (x-significance).bstr(3);
  print('%3d+  '%(significance)+'  '.join(map(b,r)));

def mtest(repeats=10) :
  """Test math functions using random real arguments"""
# acos, acosh, asin, asinh, atan, atan2, atanh,
# ceil, copysign, cos, cosh, degrees, erf, erfc, exp, expm1,
# fabs*, factorial*, floor, fmod*, frexp, fsum, gamma, gcd+, hypot,
# isclose, isfinite*, isinf*, isnan*, ldexp*, lgamma, log, log10, log1p, log2,
# modf, pow, radians, sin, sinh, sqrt, tan, tanh, trunc*
# NOT IN math: combinations-, bernoulli-, integral
# *: not tested below
# +: not explicitly tested, but is integral to rational implementation
# -: tested as part of lgamma computation
  rel_tol = rational(1,1<<set_significance());
  for i in xrange(repeats) :
    u = random();
    x,y = floor(u),ceil(u);
    if not x <= u <= y or y-x != 1 and y != x :
      print('floor-u-ceil: %s <=? %s <=? %s'%(x.bstr(30),u.bstr(30),y.bstr(30)));
    m,p = frexp(u);
    if not (isint(p) and (not (m or p) or  .5 <= abs(m) < 1) and u == m*2**p) :
      print('frexp: %s ~ %s*2**%s'%(u.bstr(30),m.bstr(30),p.bstr(30)));
    y = ldexp(m,p);
    if u != y :
      print('ldexp(frexp(%s)) ~ %s'%(u,y));
    x = (u-half)<<8;
    f,i = modf(x);
    if i+f != x or not 0<=abs(f)<1 or copysign(1,i) != copysign(1,f) :
      print('sum(modf(%s)) ~ %s + %s'%(x.bstr(30),i.bstr(30),f.bstr(30)));
    x = (u-half)*360;
    y = degrees(radians(x));
    if x != y :
      print('degrees(radians(%s) ~ %s'%(x.btr(30),y.btr(30)));
    y = sqrt(u)**2;
    if not isclose(u,y,rel_tol=rel_tol) :
      print('sqrt(%s)**2) ~ %s'%(u.bstr(30),y.bstr(30)));
    y = exp(log(u));
    if not isclose(u,y,rel_tol=rel_tol) :
      print('exp(log(%s)) ~ %s'%(u.bstr(30),y.bstr(30)));
    y = pow(2,log2(u));
    if not isclose(u,y,rel_tol=rel_tol) :
      print('pow(2,(log2(%s)) ~ %s'%(u.bstr(30),y.bstr(30)));
    y = pow(10,log10(u));
    if not isclose(u,y,rel_tol=rel_tol) :
      print('pow(10,(log10(%s)) ~ %s'%(u.bstr(30),y.bstr(30)));
    x = u/(1<<128);
    y = expm1(log1p(x));
    if not isclose(x,y,rel_tol=rel_tol) :
      print('expm1(log1p(%s)) ~ %s'%(x.bstr(30),y.bstr(30)));
    y = log1p(expm1(x));
    if not isclose(x,y,rel_tol=rel_tol) :
      print('log1p(expm1(%s)) ~ %s'%(x.bstr(30),y.bstr(30)));
    x = pi*u;
    y = acos(cos(x));
    if not isclose(x,y,rel_tol=rel_tol) :
      print('acos(cos(%s)) ~ %s'%(x.bstr(30),y.bstr(30)));
    x = pi*(u-half);
    y = asin(sin(x));
    if not isclose(x,y,rel_tol=rel_tol) :
      print('asin(sin(%s)) ~ %s'%(x.bstr(30),y.bstr(30)));
    y = atan(tan(x));
    if not isclose(x,y,rel_tol=rel_tol) :
      print('atan(tan(%s)) ~ %s'%(x.bstr(30),y.bstr(30)));
    x = 128*u
    y = acosh(cosh(x));
    if not isclose(x,y,rel_tol=rel_tol) :
      print('acosh(cosh(%s)) ~ %s'%(x.bstr(30),y.bstr(30)));
    x = 128*(u-half);
    y = asinh(sinh(x));
    if not isclose(x,y,rel_tol=rel_tol) :
      print('asinh(sinh(%s)) ~ %s'%(x.bstr(30),y.bstr(30)));
    y = atanh(tanh(x));
    if not isclose(x,y,rel_tol=rel_tol) :
      print('atanh(tanh(%s)) ~ %s'%(x.bstr(30),y.bstr(30)));
    x = tau*(u-half);
    c = cos(x);
    s = sin(x);
    y = hypot(c,s);
    if not isclose(y,1,rel_tol=rel_tol) :
      print('hypot(cos,sin(%s)) ~ %s'%(x.bstr(30),y.bstr(30)));
    y = atan2(s,c);
    if not isclose(x,y,rel_tol=rel_tol) :
      print('atan2(sin,cos(%s)) ~ %s'%(x.bstr(30),y.bstr(30)));
    x = 16*u + 1;
    y = gamma(x);
    z = gamma(x+1);
    if not isclose(x*y,z,rel_tol=rel_tol) :
      print('x, x*gamma(x) ~ gamma(x+1): %s, %s ~ %s'%(x.bstr(30),y.bstr(30),z.bstr(30)));
    y = log(y);
    z = lgamma(x);
    if not isclose(y,z,rel_tol=rel_tol) :
      print('x, ln(gamma(x)) ~ lgamma(x): %s, %s ~ %s'%(x.bstr(30),y.bstr(30),z.bstr(30)));
    x = 16*u;
    y = erf(x);
    z = erfc(x);
    if not isclose(y+z,1,rel_tol=rel_tol) :
      print('x, erf(x) + erfc(x) ~ 1 : %s, %s+%s = %s'%(x.bstr(30),y.bstr(30),z.bstr(30),(y+z).bstr(30)));
    x = integral(lambda x:x**3,u-1,u); # tests fsum as well
    y = (u**4-(u-1)**4)/4;
    if not isclose(x,y,rel_tol=rel_tol) :
      print('integral(x**3,%s,%s) = %s ~ %s'%(u-1,u,x,y));
  x = qpi;
  y = 2*atan(rational(2,11))+3*atan(rational(1,7));
  if not isclose(x,y,rel_tol=rel_tol) :
    print('2*atan(2/11)+3*atan(1/7)=%s ~ pi/4 (%s)'%(y.bstr(30),x.bstr(30)));
  # out-of-range real args...
  # acosh(0), acosh(-1), asin(2), asin(-2), acos(2), acos(-2)
  for f,finv,x in ((tanh,atanh,2),(tanh,atanh,-2),(cosh,acosh,0),(cosh,acosh,-1),(sin,asin,2),(sin,asin,-2),(cos,acos,2),(cos,acos,-2)) :
    x = rational(x);
    y = f(finv(x));
    if not isclose(x,y,rel_tol=rel_tol) :
      print('%s(%s(%s)) ~ %s'%(f.__name__,finv.__name__,x.bstr(30),y.bstr(30)));

def mxtest(repeats=10) :
  """Test trig functions with random complex args"""
# cos, sin, tan, cosh, sinh, tanh
  rel_tol = rational(1,1<<set_significance());
  for i in xrange(repeats) :
    u = random();
    v = random();
    x = 2*v*exp(xrational(0,tau*(u-half)));
    y = tan(atan(x));
    if not isclose(x,y,rel_tol=rel_tol) :
      print('tan(atan(%s)) ~ %s'%(x.bstr(30),y.bstr(30)));
    y = cos(acos(x));
    if not isclose(x,y,rel_tol=rel_tol) :
      print('cos(acos(%s)) ~ %s'%(x.bstr(30),y.bstr(30)));
    y = sin(asin(x));
    if not isclose(x,y,rel_tol=rel_tol) :
      print('sin(asin(%s)) ~ %s'%(x.bstr(30),y.bstr(30)));
    y = tanh(atanh(x));
    if not isclose(x,y,rel_tol=rel_tol) :
      print('tanh(atanh(%s)) ~ %s'%(x.bstr(30),y.bstr(30)));
    y = cosh(acosh(x));
    if not isclose(x,y,rel_tol=rel_tol) :
      print('cosh(acosh(%s)) ~ %s'%(x.bstr(30),y.bstr(30)));
    y = sinh(asinh(x));
    if not isclose(x,y,rel_tol=rel_tol) :
      print('sinh(asinh(%s)) ~ %s'%(x.bstr(30),y.bstr(30)));

def gtest(repeats=64) :
  """Test lgamma with random complex args"""
  rel_tol = rational(1,1<<set_significance());
  for i in xrange(repeats) :
    x = xrational(512*(random()-.5),8*(random()-.5));
    y = lgamma(x+1)-lgamma(x);
    if y.imag :
      y = xrational(y.real,(y.imag+pi)%tau-pi);
    z = log(x);
    if z.imag :
      z = xrational(z.real,(z.imag+pi)%tau-pi);
    if not (isclose(z.real,y.real,rel_tol=2*rel_tol) and
            isclose(z.imag,y.imag,rel_tol=0,abs_tol = tau*rel_tol)) :
      print('(lgamma(z+1)-lgamma(z=%s)).exp() ~ %s'
            %(x.bstr(30),y.exp().bstr(30)));

def stest(repeats=10) :
  """Test math functions against higher-significance results"""
  for i in xrange(repeats) :
    u = random();
    sig = set_significance();
    dig = int(ceil(sig/log2(10)));
    rel_tol = rational(1,1<<sig);
    set_significance(sig);
    x = u-half;
    y = exp(x);
    set_significance(sig+10);
    z = exp(x);
    if not isclose(y,z,rel_tol=rel_tol) :
      print('exp(%s): %s ~ %s'%(x.bstr(dig+3),y.bstr(dig),z.bstr(dig+3)))
    set_significance(sig);
    x = u
    y = log(x);
    set_significance(sig+10);
    z = log(x);
    if not isclose(y,z,rel_tol=rel_tol) :
      print('log(%s): %s ~ %s'%(x.bstr(dig+3),y.bstr(dig),z.bstr(dig+3)))
    set_significance(sig);
    x = u*tau;
    y = sin(x);
    set_significance(sig+10);
    z = sin(x);
    if not isclose(y,z,rel_tol=rel_tol) :
      print('sin(%s): %s ~ %s'%(x.bstr(dig+3),y.bstr(dig),z.bstr(dig+3)))
    set_significance(sig);
    y = cos(x);
    set_significance(sig+10);
    z = cos(x);
    if not isclose(y,z,rel_tol=rel_tol) :
      print('cos(%s): %s ~ %s'%(x.bstr(dig+3),y.bstr(dig),z.bstr(dig+3)))
    set_significance(sig);
    y = tan(x);
    set_significance(sig+10);
    z = tan(x);
    if not isclose(y,z,rel_tol=rel_tol) :
      print('tan(%s): %s ~ %s'%(x.bstr(dig+3),y.bstr(dig),z.bstr(dig+3)))
    set_significance(sig);
    x = 2*u-1;
    y = asin(x);
    set_significance(sig+10);
    z = asin(x);
    if not isclose(y,z,rel_tol=rel_tol) :
      print('asin(%s): %s ~ %s'%(x.bstr(dig+3),y.bstr(dig),z.bstr(dig+3)))
    set_significance(sig);
    y = acos(x);
    set_significance(sig+10);
    z = acos(x);
    if not isclose(y,z,rel_tol=rel_tol) :
      print('acos(%s): %s ~ %s'%(x.bstr(dig+3),y.bstr(dig),z.bstr(dig+3)))
    set_significance(sig);
    x = u;
    y = atan(x);
    set_significance(sig+10);
    z = atan(x);
    if not isclose(y,z,rel_tol=rel_tol) :
      print('atan(%s): %s ~ %s'%(x.bstr(dig+3),y.bstr(dig),z.bstr(dig+3)))
    set_significance(sig);
    y = atanh(x);
    set_significance(sig+10);
    z = atanh(x);
    if not isclose(y,z,rel_tol=rel_tol) :
      print('atanh(%s): %s ~ %s'%(x.bstr(dig+3),y.bstr(dig),z.bstr(dig+3)))
    set_significance(sig);
    x = 8*u;
    y = sinh(x);
    set_significance(sig+10);
    z = sinh(x);
    if not isclose(y,z,rel_tol=rel_tol) :
      print('sinh(%s): %s ~ %s'%(x.bstr(dig+3),y.bstr(dig),z.bstr(dig+3)))
    set_significance(sig);
    y = cosh(x);
    set_significance(sig+10);
    z = cosh(x);
    if not isclose(y,z,rel_tol=rel_tol) :
      print('cosh(%s): %s ~ %s'%(x.bstr(dig+3),y.bstr(dig),z.bstr(dig+3)))
    set_significance(sig);
    x = 8*u;
    y = tanh(x);
    set_significance(sig+10);
    z = tanh(x);
    if not isclose(y,z,rel_tol=rel_tol) :
      print('tanh(%s): %s ~ %s'%(x.bstr(dig+3),y.bstr(dig),z.bstr(dig+3)))
    set_significance(sig);
    x = 8*(u-half);
    y = asinh(x);
    set_significance(sig+10);
    z = asinh(x);
    if not isclose(y,z,rel_tol=rel_tol) :
      print('asinh(%s): %s ~ %s'%(x.bstr(dig+3),y.bstr(dig),z.bstr(dig+3)))
    set_significance(sig);
    x = 1+8*u;
    y = acosh(x);
    set_significance(sig+10);
    z = acosh(x);
    if not isclose(y,z,rel_tol=rel_tol) :
      print('acosh(%s): %s ~ %s'%(x.bstr(dig+3),y.bstr(dig),z.bstr(dig+3)))
    set_significance(sig);
    x = 1+u;
    y = gamma(x);
    set_significance(sig+10);
    z = gamma(x);
    if not isclose(y,z,rel_tol=rel_tol) :
      print('gamma(%s): %s ~ %s'%(x.bstr(dig+3),y.bstr(dig),z.bstr(dig+3)))
    set_significance(sig);
    y = lgamma(x);
    set_significance(sig+10);
    z = lgamma(x);
    if not isclose(y,z,rel_tol=rel_tol) :
      print('lgamma(%s): %s ~ %s'%(x.bstr(dig+3),y.bstr(dig),z.bstr(dig+3)))
    set_significance(sig);
    x = 16*u;
    y = erf(x);
    set_significance(sig+10);
    z = erf(x);
    if not isclose(y,z,rel_tol=rel_tol) :
      print('erf(%s): %s ~ %s'%(x.bstr(dig+3),y.bstr(dig),z.bstr(dig+3)))
    set_significance(sig);
    y = erfc(x);
    set_significance(sig+10);
    z = erfc(x);
    if not isclose(y,z,rel_tol=rel_tol) :
      print('erfc(%s): %s ~ %s'%(x.bstr(dig+3),y.bstr(dig),z.bstr(dig+3)))
    set_significance(sig);
    y = fsum(rational((-1)**i,i+1) for i in xrange(4096));
    set_significance(sig+10);
    z = fsum(rational((-1)**i,i+1) for i in xrange(4096));
    if not isclose(y,z,rel_tol=rel_tol) :
      print('fsum(1-1/2+1/3-...): %s ~ %s'%(y.bstr(dig),z.bstr(dig+3)));
    set_significance(sig);

def timingtest() :
  """Timing test"""
  timing('abs(real)','abs(r[i])',16384);
  timing('abs(complex)','abs(r[i])',plex=1);
  timing('abs(quatern)','abs(r[i])',plex=2);
  timing('abs2(real)','r[i].abs2()',16384);
  timing('abs2(complex)','r[i].abs2()',plex=1);
  timing('abs2(quatern)','r[i].abs2()',plex=2);
  timing('maxnorm(real)','r[i].maxnorm()',16384);
  timing('maxnorm(comp)','r[i].maxnorm()',plex=1);
  timing('maxnorm(quat)','r[i].maxnorm()',plex=2);
  timing('real    +','r[i]+r[i+1]',4096,nargs=2);
  timing('complex +','r[i]+r[i+1]',4096,nargs=2,plex=1);
  timing('quatern +','r[i]+r[i+1]',4096,nargs=2,plex=2);
  timing('real    *','r[i]*r[i+1]',4096,nargs=2);
  timing('complex *','r[i]*r[i+1]',4096,nargs=2,plex=1);
  timing('quatern *','r[i]*r[i+1]',4096,nargs=2,plex=2);
  timing('real    /','r[i]/r[i+1]',4096,nargs=2);
  timing('complex /','r[i]/r[i+1]',4096,nargs=2,plex=1);
  timing('quatern /','r[i]/r[i+1]',4096,nargs=2,plex=2);
  timing('real    **','u[i]**r[i+1]',nargs=2);
  timing('complex **','r[i]**r[i+1]',nargs=2,plex=1);
  timing('1/real   ','1/r[i]',16384);
  timing('1/complex','1/r[i]',4096,plex=1);
  timing('1/quatern','1/r[i]',4096,plex=2);
  timing('real**-1','r[i]**-1',16384);
  timing('complex**-1','r[i]**-1',4096,plex=1);
  timing('quatern**-1','r[i]**-1',4096,plex=2);
  timing('approximate','r[i].approximate(1<<(set_significance()-8))',4096);
  timing('exp(real)','exp(r[i])');
  timing('exp(complex)','exp(r[i])',plex=1);
  timing('exp(quatern)','exp(r[i])',plex=2);
  timing('log(real)','log(u[i])');
  timing('log(complex)','log(r[i])',plex=1);
  timing('log(quatern)','log(r[i])',plex=2);
  timing('sin(real)','sin(r[i])');
  timing('sin(complex)','sin(r[i])',plex=1);
  timing('cos(real)','cos(r[i])');
  timing('cos(complex)','cos(r[i])',plex=1);
  timing('tan(real)','tan(r[i])');
  timing('tan(complex)','tan(r[i])',plex=1);
  timing('asin(real)','asin(r[i])');
  timing('asin(complex)','asin(r[i])',plex=1);
  timing('acos(real)','acos(r[i])');
  timing('acos(complex)','acos(r[i])',plex=1);
  timing('atan(real)','atan(r[i])');
  timing('atan(complex)','atan(r[i])',plex=1);
  timing('sinh(real)','sinh(r[i])');
  timing('sinh(complex)','sinh(r[i])',plex=1);
  timing('cosh(real)','cosh(r[i])');
  timing('cosh(complex)','cosh(r[i])',plex=1);
  timing('tanh(real)','tanh(r[i])');
  timing('tanh(complex)','tanh(r[i])',plex=1);
  timing('asinh(real)','asinh(r[i])');
  timing('asinh(complex)','asinh(r[i])',plex=1);
  timing('acosh(real)','acosh(1/u[i])');
  timing('acosh(complex)','acosh(r[i])',plex=1);
  timing('atanh(real)','atanh(r[i])');
  timing('atanh(complex)','atanh(r[i])',plex=1);
  timing('erf(real)','erf(r[i])');
  timing('erf(complex)','erf(r[i])',plex=1);
  timing('erfc(real)','erfc(r[i])');
  timing('erfc(complex)','erfc(r[i])',plex=1);
  timing('gamma(real)','gamma(u[i])');
  timing('gamma(complex)','gamma(r[i])',plex=1);
  timing('lgamma(real)','lgamma(u[i])');
  timing('lgamma(complex)','lgamma(r[i])',plex=1);
  timing('fsum(unsigned)','fsum(u)',4096);
  timing('fsum(real)', 'fsum(r)',4096);
  timing('fsum(complex)','fsum(r)',4096,plex=1);
  timing('fsum(quatern)','fsum(r)',4096,plex=2);

if __name__ == '__main__' :
  print('root test (for sha2) ...');
  roottest();
  print('rational test ...');
  rattest();
  print('xrational test ...');
  xtest();
  print('qrational test ...');
  qtest();
  print('mixed rational test ...');
  mixtest();
  print('vector product test ...');
  vtest();
  print('approximate test ...')
  atest();
  print('math methods test');
  mtest();
  print('trig(complex) test');
  mxtest();
  print('lgamma test');
  gtest();
  print('significance test');
  stest();
  print('timing test');
  timingtest();
  print('transcendental function accuracy test ...');
  for significance in xrange(MIN_SIGNIFICANCE,MAX_SIGNIFICANCE+1,gcd(MIN_SIGNIFICANCE,MAX_SIGNIFICANCE)) :
    ttest(significance,significance==MIN_SIGNIFICANCE);

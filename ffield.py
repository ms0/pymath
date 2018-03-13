""" finite field classes """

import sys

if sys.version_info>(3,) :
  unicode = str;
  xrange = range;
  range = lambda *x: list(xrange(*x));
  long = int;  
  xmap = map;
  map = lambda *x: list(xmap(*x));

# finite field class

import pdb

import random
random.seed();
from math import floor,log

def modpow(b,x,p) :    # b**x mod p
  """Compute b**x%p"""
  if not x : return 1;
  n = 1 << int(floor(log(x,2)));
  while x >= n << 1 : n <<= 1;
  e = 1;
  while n :
    e *= e;
    e %= p;
    if x&n :
      e *= b;
      e %= p;
    n >>= 1;
  return e;

primalitytestlimit = 1<<24;    # limit for looking for (odd) divisor
# beyond this limit, use Miller-Rabin
  
def isprime(n) :
  """Test if n is prime, if no "small" factors, use probabilistic Miller-Rabin test"""
  if not isinstance(n,(int,long)) or n < 2 or (not n%2 and n!=2) : return False;
  if n < 9 : return True;
  i = 3;
  while i < primalitytestlimit :
    q = n//i;
    if not (n-i*q) : return False;
    if q <= i : return True;
    i += 2;
  # Miller Rabin test
  c = n//2;    # (n-1)/2
  b = 1;       # n = 2**b * c
  while not c&1 :
    c >>= 1;
    b += 1;
  for i in xrange(100) :
    a = random.randrange(1,n);
    e = pow(a,c,n);
    if e == 1 : continue;
    for i in xrange(b) :
      if e == n-1 : break;
      e = pow(e,2,n);
      if e == 1 : return False;
    else :
      return False;    # didn't get to -1
  return True;


# test for irreducibility [Rabin]
# let p be our prime, and n our exponent
# let q1, q2,..., qk be all the distinct prime divisors of n, in ascending order
# let f be a monic polynomial in Fp[x] of degree n
# for j = 1 thru k
#   nj = n/qj
# for i = 1 thru k
#   h = x**p**ni - x mod f
#   g = gcd(f,h)
#   if g != 1, f is reducible
# g = x**p**n - x mod f
# if g != 0 f is reducible
# else f is irreducible

def isirreducible(poly,p) :  # missing leading coefficient assumed to be 1
  """Run the deterministic Rabin test to see if poly over GF(p) is irreducible;
poly is represented as a tuple of coefficients ending with the constant term, but
without the leading coefficient, which is taken to be 1"""
  n = len(poly);
  if n <= 1 : return True;
  x = (1,0);
  q = factors(n);
  k = len(q);
  f = (1,)+poly;
  for i in xrange(k) :
    if len(mpgcd(p,f,mpsub(p,mppow(p,x,p**(n//q[i]),f),x))) != 1 : return False;
  return not mpdivrem(p,mpsub(p,mppow(p,x,p**n,f),x),f)[1];

def factors(n) :
  """Return the prime factors of n in increasing order"""
  if n <= 1 : return ();
  q = [];    # list of factors
  while not n&1 :
    if not q or q[-1] != 2 : q.append(2);
    n >>= 1;
  p = 3;
  while n > 1 :
    if p*p > n :
      q.append(n);      
      break;
    while not n % p :
      if not q or q[-1] != p : q.append(p);
      n //= p;
    p += 2;
  return tuple(q);

def pack(p,a) :
  """Return the evaluation at x=p of a, a tuple of coefficients ending with the constant term"""
  x = 0;
  for z in a :
    x *= p;
    x += z;
  return x;

def unpack(p,x) :
  """Return the tuple of coefficients of the polynomial over GF(p) that evaluates to |x| at p"""
  x = abs(x);
  a = [];
  while x :
    a.append(x%p);
    x //= p;
  return tuple(reversed(a));

def __init__(self,x) :
  """Create a finite field element given its polynomial representation, x
The polynomial can be represented as
  an integer with absolute value < p**n, the value (mod p**n) of the polynomial at x=p
  a tuple or list comprising at most n integers, each in [0,p);
    these are the polynomial coefficients, ending with the constant
  if p <= 36, a string of at most n zits, each having a value < p;
    these values are the polynomial coefficients, ending with the constant;
    the string is stripped and converted to lower case before evaluation;
    zit values are their positions in '0123456789abcdefghijklmnopqrstuvwxyz'
Instance variables:
 p: the characterisitic of the field (inherited from the type)
 n: the degree of the polynomial modulus (inherited from the type)
 x: the polynomial representation, evaluated at x=p"""
  if isinstance(x,self.__class__) :
    self.x = x.x;
    return;
  p = self.p;
  n = self.n;
  if isinstance(x,(int,long)) :
    pn = p**n;
    if -pn < x < pn :
      self.x = x%pn;
    else : raise ValueError('absolute value must be < %d'%(pn));
  elif isinstance(x,(tuple,list)) :
    if len(x) > n :
      raise ValueError('tuple must have length at most %d'%(n)) ;
    else :
      s = 0;
      for i in x :
        if not isinstance(i,(int,long)) :
          raise TypeError('tuple elements must be integers');
        if not 0 <= i < p :
          raise ValueError('tuple elements must be in [0,%d)'%(p));
        s *= p
        s += i;
      self.x = s;
  elif isinstance(x,(str,unicode)) and p <= 36 : # allow sequence of base-p chars if p <= 36
    if len(x) > n : raise ValueError('string must be at most n zits long')
    try:
      s = x.strip().lower();
      x = 0;
      for c in s :
        x = x*p + zits[:p].index(c);    # will raise ValueError if illegal
    except ValueError :
      raise ValueError('zits in string must be in "%s"'%(zits[:p]));
    self.x = x;
  else : raise TypeError;

def __getattr__(self,name) :
  if name == 'tupoly' :
    return self._tupoly[self._nzi:];
  if name == 'order' :
    o = self.p**self.n-1;
    if isinstance(self,ffield) :
      return o;
    if self.x <= 1 :
      return self.x;
    while True :
      q = factors(o);
      for p in q :
        if (self**(o//p)).x == 1 : break;    # order is divisor of o//p
      else :
        return o;
      o //= p;
  raise AttributeError('%s has no attribute %s'%(self.__class__.__name__,name));

def __hash__(self) :
  return hash(self.__class__) ^ hash(self.x);

def __eq__(self,other) :
  """Test if two elements are in the same class and have the same value"""
  return self.__class__ == other.__class__ and self.x == other.x;

def __ne__(self,other) :
  """Test if two elements are in different classes or have different values"""
  return self.__class__ != other.__class__ or self.x != other.x;

__le__ = __ge__ = __eq__;
__lt__ = __gt__ = lambda x,y:False;

def __nonzero__(self) :
  return self.x != 0;

def __str__(self) :
  """Return a string representing the polynomial representation of the finite field element
If n = 1, return the value as a decimal integer, the polynomial evaluated at x=p
Otherwise, return the coefficients in sequence ending with the constant term;
if p <= 36, each coefficient is a zit; else each is a decimal integer, period separated"""
  x = self.x;
  n = self.n;
  p = self.p;
  if n == 1 : return '%d'%(x);
  a = [];
  for i in xrange(n) :
    a.append(x%p);
    x //= p;
  a.reverse();
  if p > 36 :
    return '.'.join(map(lambda x:'%d'%(x),a));
  return ''.join(map(lambda x: zits[x],a));

def __repr__(self) :
  """Return a string representing the polynomial representation of the finite field element
The string begins with the characterisitic of the field as a decimal integer and is followed
by an underscore and the __str__ representation"""
  return str(self.p)+'_'+str(self);

def __add__(self,other) :
  """Return the sum of the two finite field elements; integers are treated mod p"""
  p = self.p;
  n = self.n;
  x = self.x;
  if not isinstance(other,self.__class__) :
    if isinstance(other,(int,long)) :
      other %= p;
      if not other : return self;
      return self.__class__(x-x%p+(x+other)%p);
    else :
      raise TypeError('must be field element');
  y = other.x;
  if not y : return self;
  if p == 2 :
    return self.__class__(x^y);
  if n == 1 :
    return self.__class__((x+y)%p);
  a = [];
  for i in xrange(n) :
    a.append((x+y)%p);
    x //= p;
    y //= p;
  s = 0;
  for c in reversed(a) :
    s *= p;
    s += c;
  return self.__class__(s);

def __abs__(self) :
  """Return 0 if the element is 0, else 1"""
  return 1 if self.x else 0;

def __pos__(self) :
  """Return the element"""
  return self;

def __neg__(self) :
  """Return the additive inverse of the element"""
  x = self.x;
  if not x : return self;
  p = self.p;
  n = self.n;
  if p == 2 : return self;
  if n == 1 : return self.__class__(-x%p);
  a = [];
  for i in xrange(n) :
    a.append(-x%p);
    x //= p;
  s = 0;
  for c in reversed(a) :
    s *= p;
    s += c;
  return self.__class__(s);

def __sub__(self,other) :
  """Return the difference of the two finite field elements; integers are treated mod p"""
  p = self.p;
  n = self.n;
  x = self.x;
  if not isinstance(other,self.__class__) :
    if isinstance(other,(int,long)) :
      other %= p;
      if not other : return self;
      return self.__class__(x-x%p+(x-other)%p);
    else :
      raise TypeError('must be field element');
  y = other.x;
  if not y : return self;
  if p == 2 : return self.__class__(x^y);
  if n == 1 : return self.__class__((x-y)%p);
  a = [];
  for i in xrange(n) :
    a.append((x-y)%p);
    x //= p;
    y //= p;
  s = 0;
  for c in reversed(a) :
    s *= p;
    s += c;
  return self.__class__(s);

def __rsub__(self,y) :
  """Return the difference of the swapped finite field elements; integers  are treated mod p"""
  p = self.p;
  if not isinstance(y,(int,long)) :
    raise TypeError('must be field element');
  return self.__class__(y%p)-self;

def __div__(self,y) :
  """Return the quotient of the two finite field elements; integers are treated mod p"""
  p = self.p;
  x = self.x;
  n = self.n;
  if not isinstance(y,self.__class__) :
    if isinstance(y,(int,long)) :
      y %= p;
      if not y : raise ZeroDivisionError;
      if y == 1 : return self;
      d = pow(y,p-2,p);
      a = [];
      for i in xrange(n) :
        a.append(x*d%p);
        x //= p;
      s = 0;
      for c in reversed(a) :
        s *= p;
        s += c;
      return self.__class__(s);
    else : raise TypeError;
  yx = y.x;
  if yx < p : return self/yx;
  return self*self.__class__(pack(p,xmpgcd(p,self._tupoly,unpack(p,yx))[2]));
#  return self*y**(p**n-2);

def __rdiv__(self,y) :    # y/self
  """Return y/self; y must be an integer and is interpreted mod p"""
  p = self.p;
  if not isinstance(y,(int,long)) :
    raise TypeError('must be field element');
  x = self.x;
  if not x : raise ZeroDivisionError;
  y %= p;
  if x < p :
    z = y*pow(x,p-2,p)%p;
  else :
    z = 0;
    for i in xmpgcd(p,self._tupoly,unpack(p,x))[2] :
      z = p*z+i*y%p;
  return self.__class__(z);

def __mul__(self,y) :
  """Return the product of the two finite field elements; integers are treated mod p"""
  p = self.p;
  x = self.x;
  n = self.n;
  if not isinstance(y,self.__class__) :
    if isinstance(y,(int,long)) :
      d = y%p;
      if not d : return self.__class__(0);
      if d == 1 : return self;
      a = [];
      for i in xrange(n) :
        a.append(x*d%p);
        x //= p;
      s = 0;
      for c in reversed(a) :
        s *= p;
        s += c;
      return self.__class__(s);
    else : raise TypeError('must be field element');
  if n == 1 :
    return self.__class__(x*y.x%p);
  if p == 2 :
    y = y.x;
    g = self.poly;
    xy = 0;
    M = 1<<(n-1);
    N = M-1
    m = M;
    while m :
      xy = (((xy&N)<<1)^g if xy&M else xy<<1);
      if y&m : xy ^= x;
      m >>= 1;
    return self.__class__(xy);
  return self.__class__(pack(p,mpmul(p,unpack(p,x),unpack(p,y.x),self._tupoly)));

def __pow__(self,e) :
  """Raise the finite field element to the specified power mod p**n-1, 0**0=0"""
  if not isinstance(e,(int,long)) :
    raise TypeError('power must be integer');
  x = self.x;
  if x <= 1 : return self;    # this differs from pow result for 0**0
  p = self.p;
  n = self.n;
  e %= p**n-1;
  if e == 0:
    x = 1;
  elif e == 1 :
    return self;
  elif x < p :
    x = pow(x,e,p);
  else :
    x = pack(p,mppow(p,unpack(p,x),e,self._tupoly));
  return self.__class__(x);


class ffield(type) :
  """Class to create finite field class for GF(p**n)
Field elements are represented as polynomials over GF(p) with degree < n.
Arithmetic is done modulo a specified irreducible monic polynomial of degree n.
That polynomial modulus is represented as a tuple of coefficients, length <= n,
constant term last; the coefficient of x**n is elided and assumed to be 1,
immediately following zero coefficients may also be elided.
The polynomial is also stored as its value at x=p, again without the x**n term.
The polynomial modulus can be specified in either of those ways.
Instance variables:
  p: characteristic (a prime)
  n: dimension (giving the field p**n elements)
  tupoly: the polynomial modulus's tuple representation
  poly: an integer giving the value of tupoly at x = p
  _tupoly: the unelided polynomial modulus as a tuple with first element 1
Methods: __new__, __hash__, __eq__, __ne__, __lt__, __le__, __ge__, __gt__

Each instance of the created type is an element of the finite field:
Instance variables:
  x: the value at p of the polynomial representing the element
Methods: __init__, __hash__, __repr__, __str__,
         __abs__, __pos__, __neg__,
         __nonzero__, __eq__, __ne__,
         __add__, __radd__, __sub__, __rsub__,
         __mul__, __rmul__, __div__, __rdiv__, __truediv__, __rtruediv__,
         __pow__
"""

  def __new__(cls,p,n=1,poly=0) :
    if p < 2 or not isprime(p) :
      raise ValueError('Not prime');
    if  n < 1 or not isinstance(n,(int,long)) :
      raise ValueError('Bad power');
    if isinstance(poly,(int,long)) :
      if not 0 <= poly < p**n : raise ValueError('Bad poly');
    elif isinstance(poly,tuple) and len(poly) <= n :
      tupoly = poly;
      poly = 0;
      for c in tupoly :
        if not (isinstance(c,(int,long)) and 0 <= c < p) :
          raise ValueError('Bad poly');
        poly = p*poly + c;
    else : raise ValueError('Bad poly');
    tupoly = unpack(p,poly);
    _nzi = -len(tupoly);
    _tupoly = (1,)+(n+_nzi)*(0,)+tupoly;
    if not isirreducible(_tupoly[1:],p) :
      raise ValueError('Composite poly');
    d = dict(p=p,n=n,poly=poly,_tupoly=_tupoly,_nzi=_nzi,
             __init__=__init__,
             __getattr__=__getattr__,
             __repr__=__repr__,
             __str__=__str__,
             __hash__=__hash__,
             __eq__=__eq__,
             __ne__=__ne__,
             __lt__=__lt__,
             __le__=__le__,
             __gt__=__gt__,
             __ge__=__ge__,
             __nonzero__=__nonzero__,
             __neg__=__neg__,
             __pos__=__pos__,
             __add__=__add__,
             __radd__=__add__,
             __sub__=__sub__,
             __rsub__=__rsub__,
             __mul__=__mul__,
             __rmul__=__mul__,
             __div__=__div__,
             __truediv__=__div__,
             __rdiv__=__rdiv__,
             __rtruediv__=__rdiv__,
             __pow__=__pow__,
             __abs__=__abs__,
            );
    # need to define all the relevant operators:
    # comparisons: only == and !=
    # pow, with exponent being integer (int or long) or GF(p**n-1)
    # mul, div,
    # neg[-], pos[+], abs, no invert [~]    
    # add, sub, neg (only in same class)
    # no and, or, xor
    # repr, str
    # hash
    # NO: i* because want these things to be immutable
    # see https://docs.python.org/2/reference/datamodel.html

    name = ('GF%d'%(p) if n == 1 else
            'GF%d_%d_%s'%(p,n,''.join([zits[c] for c in tupoly])) if p <= 36 else
            'GF%d_%d_%s'%(p,n,'_'.join(['%d'%(c) for c in tupoly])));
    return type.__new__(cls,name,(),d);

  __getattr__ = __getattr__

  def __hash__(self) :
    return hash(self.__class__)^hash('%s:%s'%(self.p**self.n,self.poly));

  def __eq__(self,other) :
    return self.__class__==other.__class__ and self.p==other.p and self.n==other.n and self.poly==other.poly;
  
  def __ne__(self,other) :
    return not self==other;

  __le__ = __eq__;
  __ge__ = __eq__;
  __lt__ = __lt__;
  __gt__ = __gt__;

zits='0123456789abcdefghijklmnopqrstuvwxyz';

# how do we display an instance ?
# possibility 0:
#   non-negative integer: coeff(g**0)+p*(coeff(g**1)+p*(...coeff(g**(n-1))...))
# possibility 1:
#  if n = 1, just the non-negative integer, in decimal
#  if n > 1, a tuple of non-negative integers: coeffs of g**(n-1), ...g**1, g**0
# possibility 1r:
#  if n > 1, a tuple of non-negative integers: coeffs of g**0, g**1, ...g**(n-1)
# possibility 2:
#  if p <= 36, base p representation of possibility 0
#  else, possibility 0
# possibility 3:
#  if p == 2, hexadecimal of possibility 0
#  else, possibility 2

# mul is hardest
# pow exponent must be integer
# div (all versions) is same, and uses pow(-1) = pow(p**n-2); divide by zero raises Error
# no rdiv? but rmul


# NOTE, if polynomial is not irreducible, the class is still a ring.
# We can still multiply polynomials mod poly
# We can still perform gcd.

def gcd(a,b):
  """Return the gcd of integers a and b"""
#  want ua + vb = g
#  have u[i]*a + v[i]*b = r[i]
#  u[-2] = 1, v[-2] = 0, r[-2] = a
#  u[-1] = 0, v[-1] = 1, r[-1] = b
#  if r[n-2] = q*r[n-1] + r[n],
#  un = u[n-2]-q*u[n-1]
#  vn = v[n-2]-q*v[n-1]
  while b :
    a,b = b, a-a//b*b;
  return a;

def xgcd(a,b) :
  """Return g,u,v, where g = ua+vb is the gcd of integers a and b"""
  u0,v0,u1,v1 = 1,0,0,1;
  while b :
    q = a//b;
    a,b = b,a-q*b;
    u0,v0,u1,v1 = u1,v1,u0-q*u1,v0-q*v1;
  return a,u0,v0;

# modular polynomial functions
# polynomials represented as tuples of mod p integers, hi to lo
# note 1/x = x**(p-2)

def mpmul(p,f,g,m=None) :
  """Return the product of f and g, polynomials over GF(p), modulo polynomial m"""
  while f and not f[0] : f = f[1:];
  while g and not g[0] : g = g[1:];
  if not f or not g : return ();
  fg = (len(f)+len(g)-1)*[0];
  for i in xrange(len(f)) :
    for j in xrange(len(g)) :
      fg[i+j] = (fg[i+j]+f[i]*g[j])%p;
  while fg and not fg[0] : fg = fg[1:];
  return tuple(fg) if not m else mpdivrem(p,fg,m)[1];

def mpadd(p,f,g) :
  """Return the sum of f and g, polynomials over GF(p)"""
  while f and not f[0] : f = f[1:];
  while g and not g[0] : g = g[1:];
  lf = len(f);
  lg = len(g);
  if lf < lg : lf,lg,f,g = lg,lf,g,f;
  ld = lf-lg;
  s = list(f);
  for i in xrange(lg) :
    s[ld+i] = (s[ld+i]+g[i])%p;
  while s and not s[0] : s = s[1:];
  return tuple(s);

def mpsub(p,f,g) :
  """Return the difference of f and g, polynomials over GF(p)"""
  n = mpneg(p,g);
  return mpadd(p,f,n)

def mpneg(p,f) :
  """Return the additive inverse of f, a polynomial over GF(p)"""
  while f and not f[0] : f = f[1:];
  n = [];
  for x in f :
    n.append(-x%p);
  return tuple(n);

def mpdivrem(p,f,g) :
  """Return the quotient and remainder from dividing f by g, polynomials over GF(p)"""
  r = list(f);
  while r and not r[0] : r = r[1:];
  while g and not g[0] : g = g[1:];
  if not g : raise ZeroDivisionError;
  dr = len(r)-1;
  dg = len(g)-1;
  q = [];
  for i in xrange(dr-dg+1) :
    q.append(r[i]*pow(g[0],p-2,p)%p);
    for j in xrange(dg+1) :
      r[i+j] = (r[i+j]-q[-1]*g[j])%p;
  while r and not r[0] : r = r[1:];
  return tuple(q),tuple(r);

def mppow(p,b,e,m=None) :
  """Raise b, a polynomial over GF(p), to the nonnegative integer power e, modulo polynomial m"""
  if not e : return (1,);
  n = 1 << int(floor(log(e,2)));
  while e >= n << 1 : n <<= 1;
  x = b;
  n >>= 1;
  while n :
    x = mpmul(p,x,x,m);
    if e&n :
      x = mpmul(p,x,b,m);
    n >>= 1;
  return x;

def mpgcd(p,f,g) :
  """Return the monic gcd of f and g, all polynomials over GF(p)"""
  while f and not f[0] : f = f[1:];
  while g and not g[0] : g = g[1:];
  while g :
    f,g = g, mpdivrem(p,f,g)[1];
  return mpmul(p,f,(pow(f[0],p-2,p),)) if f and f[0] != 1 else f;

def xmpgcd(p,f,g) :
  """Return the monic gcd d of f and g, together with u,v such that d=uf+vg,
all polynomials over GF(p); note that g**-1 mod f = xmpgcd(p,f,g)[2]"""
  u0,v0,u1,v1 = (1,),(),(),(1,);
  while f and not f[0] : f = f[1:];
  while g and not g[0] : g = g[1:];
  while g :
    q,r = mpdivrem(p,f,g);
    f,g = g,r;
    u0,v0,u1,v1 = u1,v1,mpsub(p,u0,mpmul(p,q,u1)),mpsub(p,v0,mpmul(p,q,v1));
  if f and f[0] != 1:
    q = (pow(f[0],p-2,p),);
    f = mpmul(p,f,q);
    u0 = mpmul(p,u0,q);
    v0 = mpmul(p,v0,q);
  return f,u0,v0;


def test_irreducibility(p,n) :
  """Print all the irreducible polynomials of degree n over GF(p)"""
  for i in xrange(p**n) :
    poly = [];
    j = i;
    for k in xrange(n) :
      poly.append(j%p);
      j //= p;
    poly = tuple(poly);
    if isirreducible(poly,p) : print((1,)+poly);

# for first few n :
# (1,1),(1,0)
# (1,1,1)
# (1,0,1,1),(1,1,0,1)
# (1,0,0,1,1),(1,1,1,1,1),(1,1,0,0,1)
# (1,0,0,1,0,1),(1,0,1,1,1,1),(1,0,1,0,0,1),(1,1,1,0,1,1),(1,1,1,1,0,1),(1,1,0,1,1,1)
# [this has been verified, but perhaps we should put it in the test]

# some test routines that could be useful:
# test n=1 cases of +,-,*,/,** [p=31,p=17]
# test p=2 cases of " [n=8 should be fine]
# test general cases [n=3,p=5 should be good enough]
# How do we test?
#  Verify associativity, commutativity, and distributivity for random values?
#  Verify a/b*b = a for b!=0
#  Verify a-b+b = a
#  Verify 0*x = x*0 = 0
#  Verify 1*x = x*1 = x
#  Verify 0+x = x+0 = x
#  Verify multiply and divide by scalar
#  Verify 0**x = 0
#  Verify 1**x = 1
#  Verify a**(x+y) = a**x * a**y
#  Verify (ab)**x = a**x * b**x
#  Verify a*a**-1 = 1 for a!=0
# For p = 2, n = 1, we can do a full test of all possible values,
# noting that the exponent in pow is mod 1.
# Even for p = 2, n = 5, a full test would be feasible, using independent code
# For p > 2, n = 1, we can do a full test for small p (say 3 or 5)
# The general case we'll do with random test values.

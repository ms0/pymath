""" finite field classes """
from __future__ import division

__all__ = ['ffield']

import sys

import random
random.seed();

from itertools import chain, count
from matrix import matrix, product
from rational import root, rational
import poly as pn

if sys.version_info>(3,) :
  unicode = str;
  xrange = range;
  range = lambda *x: list(xrange(*x));
  isint = lambda x: isinstance(x,int);
  isstr = lambda x: isinstance(x,str);
  xmap = map;
  map = lambda *x: list(xmap(*x));
else :
  isint = lambda x: isinstance(x,(int,long));
  isstr = lambda x: isinstance(x,(str,unicode));
  _xrange = xrange
  def xrange(*a) :    # because builtin xrange has limited range
    try :
      return _xrange(*a);
    except OverflowError :
      return exrange(*a);
  def exrange(*a) :
    try :
      step = a[2];
    except IndexError :
      step = 1;
    try :
      stop = a[1];
      start = a[0];
    except IndexError :
      stop = a[0];
      start = 0;
    while start < stop :
      yield start;
      start += step;

def isffield(t) :
  """Return True iff t is a finite field"""
  if not isinstance(t,type) : return False;
  try :
    t._basefield;
    return isint(t._q);
  except Exception :
    return False;

try :
  int.bit_length;
  bit_length = lambda n : n.bit_length();
except Exception :
  import math
  def bit_length(n) :
    n = abs(n);
    b = 0;
    while n :
      try :
        l = int(math.log(n,2));
        while n >> l : l += 1;
      except OverflowError :
        l = sys.float_info.max_exp-1;
      b += l
      n >>= l;
    return b;

def bit_count(n) :
  """Return number of 1 bits in |n|"""
  return bin(n).count('1');

def bit_reverse(n) :    # empirically faster in all practical cases
  """Return bit-reversed non-negative integer"""
  return int(bin(n)[-1:1:-1],2);

def bump_bits(n) :
  """Return the next larger int with the same bit_count (for positive n)"""
  o = n&-n;  # rightmost 1
  n += o;    # carries to next 0
  n |= ((n&-n)-o)>>bit_length(o);  # restore remaining bits as LSBs
  return n;

def rint(x) :
  """If x is a rational integer, return x.numerator, else, return x"""
  return x.numerator if isinstance(x,rational) and abs(x.denominator)==1 else x;

def modpow(b,x,p) :    # b**x mod p
  """Compute b**x%p"""
  if not x : return 1;
  n = (1 << (bit_length(x)-1)) >> 1;
  e = b%p;
  while n :
    e *= e;
    e %= p;
    if x&n :
      e *= b;
      e %= p;
    n >>= 1;
  return e;

primalitytestlimit = 1<<24;    # limit for looking for (odd) divisor
# beyond this limit, use Miller-Rabin or Lucas-Lehmer

try :
  from math import gcd
except Exception :
  def gcd(x,y) :
    """Return the [nonnegative] greatest common divisor of x and y"""
    while y :
      x,y = y, x%y;
    return abs(x);

pr210 = (2,3,5,7,11,13);    # primes < sqrt(2*3*5*7)
isp210 = tuple(    # primality of integers in range(2*3*5*7)
  i in pr210 or i > pr210[-1] and all(i%p for p in pr210) for i in xrange(210));
op210 = pr210[1:] + tuple(    # odd primes < 2*3*5*7
  i for i in xrange(pr210[-1]+1,210) if isp210[i]);
isZ210 = tuple(gcd(i,210)==1 for i in xrange(210));    # relative primality mod 2*3*5*7
Z210 = tuple(i for i in xrange(210) if isZ210[i]);    # relative primes mod 2*3*5*7

def oplist(m) :    # odd primes < 2*3*5*7 then larger ints relatively prime to 2*3*5*7
  for i in op210 : yield i;
  for i in xrange(210,m,210) if m else count(210,210):    # give up after m
    for p in Z210 : yield i+p;

def oplist11(m) : # oplist, but starting at 11
  for i in op210[3:] : yield i;
  for i in xrange(210,m,210) if m else count(210,210):    # give up after m
    for d in Z210 : yield i+d;

def primes(start=2,stop=None) :
  """Generator for primes"""
  if stop is None :
    if start <= 2 :
      yield 2;
      for p in op210: yield p;
      for i in count(210,210) :
        for d in Z210 :
          p = i+d;
          if isprime(p) : yield p;
    else :
      z = start-start%210;
      if z :
        for d in Z210 :
          p = z+d;
          if start <= p and isprime(p) : yield p;
      else :
        for p in op210:
          if start <= p : yield p;
      for i in count(z+210,210) :
        for d in Z210 :
          p = i+d;
          if isprime(p) : yield p;
  elif start < stop :
    if start <= 2 < stop :
      yield 2;
    z = start-start%210;    # initial tranche
    t = stop-stop%210;      # final tranche
    if not z :    # start in [0,210)
      if t :
        for p in op210 :
          if start <= p : yield p;
      else :    # start and end in [0,210)
        for p in op210 :
          if p >= stop : return;
          if start <= p : yield p;
        return;
    else :    # start from 210 or greater
      if z < t :
        for d in Z210 :
          p = z+d;
          if start <= p and isprime(p) : yield p;
      else :    # start and end in same tranche
        for d in Z210 :
          p = z+d;
          if p >= stop : return;
          if start <= p and isprime(p) : yield p;
        return;
    for i in xrange(z+210,t,210) :    # full tranches
      for d in Z210 :
        p = i+d;
        if isprime(p) : yield p;
    for d in Z210 :    # final tranche
      p = t+d;
      if p >= stop : return;
      if isprime(p) : yield p;
  
def isprime(n) :
  """Test if n is prime, if no "small" factors,
use probabilistic Miller-Rabin test or Lucas-Lehmer test when applicable"""
  n = rint(n);
  if n < 210 : return isp210[n];
  if not isZ210[n%210] : return False;
  if n&(n+1) :    # not Mersenne number
    if (n-1)&(n-2):    # not Fermat number
      d = oplist11(primalitytestlimit);    # general primality test
    else :
      e = bit_length(n)-1;    # n = 2**e+1 [Fermat?]
      if e&(e-1) : return False;    # e not power of 2
      return pow(3,n>>1,n)==n-1;    # Pepin's test
    for p in d :
      q,r = divmod(n,p);
      if not r : return False;
      if q <= p : return True;
    # Miller Rabin test :
    c = n-1;
    b = bit_length(c&-c)-1;
    c >>= b;    # n-1 = 2**b * c
    for i in xrange(100) :
      a = random.randrange(2,n-1);
      e = pow(a,c,n);
      if e == 1 : continue;
      for i in xrange(b) :
        if e == n-1 : break;
        e = pow(e,2,n);
        if e == 1 : return False;
      else :
        return False;    # didn't get to -1
    return True;
  e = bit_length(n);    # n = 2**e-1 [Mersenne?]
  if not isprime(e) : return False;    # e not prime
  for i in xrange(2*e+1,primalitytestlimit,2*e) :
    # prime factors must be 2ke+1 and +-1 mod 8
    if (i+1)&7 > 2 or not isZ210[i%210]: continue;
    q,r = divmod(n,i);
    if not r: return False;
    if q <= i : return True;
  # Lucas-Lehmer test :
  c = 4;
  for i in xrange(e-2) :
    c = (c*c-2)%n;
  return not c;

bigp = 53;    # "big" prime
lps = set(primes(2,bigp));    # "little" primes
plps = product(lps);   # product of "little" primes

def primepower(q) :
  """Return (p,n) if q == p**n, else None"""
  g = gcd(plps,q);
  if g != 1 :
    if not g in lps : return None;
    if g == 2 :
      c = bit_length(q&-q)-1;
      q >>= c;
      return (2,c) if q==1 else None;
    for c in count(1) :
      q,r = divmod(q,g);
      if r : return None;
      if q == 1 : return (g,c);
  x = 1;
  for p in primes() :
    while True :
      if bigp**p > q : return (q,x) if isprime(q) else None;
      r = root(q,p);
      if r**p != q : break;
      x *= p;
      q = r;

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

def isirreducible(poly,q) :  # missing leading coefficient assumed to be 1
  """Run the deterministic Rabin test to see if poly is irreducible over GF(q);
q must be a positive power of a prime p; poly is represented as a tuple of
integer coefficients interpreted mod p, ending with the constant term, but
without the leading coefficient, which is taken to be 1"""
  p = primepower(q);
  if not p : raise ValueError('q must be a power of a prime');
  p,k = p;
  n = len(poly);
  if n <= 1 : return n==1;
  if not poly[-1] : return False;
  f = (1,)+poly;
  if p == 2 : return isirreducible2(pack(2,f),k);
  x = (1,0);
  for r in factors(n) :
    if len(mpgcd(p,f,mpsub(p,mppow(p,x,q**(n//r),f),x))) != 1 : return False;
  return not mpmod(p,mpsub(p,mppow(p,x,q**n,f),x),f);

# An irreducible polynomial f(x) of degree m over GF(p), where p is prime,
# is a primitive polynomial iff the smallest positive integer n such that
# f(x) | x^n - 1 is n = p^m - 1.

def isprimitive(g,p) :
  """Return True iff monic irreducible g is a primitive polynomial over GF(p);
  g is represented as a tuple or list of integers mod p without the leading 1"""
  n = len(g);
  if p == 2 : return isprimitive2((1<<n)|pack(2,g));
  q = primepower(p);
  if not q : raise ValueError('p must be a prime');    # but allow prime power
  if q[1] != 1 or not g[-1] : return False;
  if n == 1 and g[0] == p-1 : return False;    # x-1
  o = p**n-1;
  # simple algorithm:
  #   for f in factors(o) :
  #     d = (1,)*(o//f);    # (x**(o//f)-1)/(x-1)
  #     if not mpmod(p,d,g) : return False;
  #   return True;
  # this instead tests all factors at once and with little memory:
  d = [1]*(2*n);    # we concatenate 1s as we divide
  i = 0;    # index (in d) of first nonzero coefficient
  for _ in xrange(o//2-n) :    # implicitly check through o//2
    q = d[i];    # leading coefficient of dividend
    for j in xrange(n) :    # compute remainder so far
      d[j] = (d[i+j+1]-q*g[j])%p;
    for i in xrange(n) :
      if d[i] : break;    # new leading coefficient
    else :
      return False;    # remainder was 0, so g divides x**m-1 for m < p**n-1
  return True;    

def factors(n,maxfactor=None) :
  """Return the prime factors of n in increasing order as a generator"""
  for p in factor(n,maxfactor) : yield p[0];

def factor(n,maxfactor=None) :
  """Return prime factorization of n as generator of (prime,exponent) pairs"""
  n = abs(n);
  if n <= 1 :
    return;
  if not n & 1:
    c = bit_length(n&-n)-1;
    n >>= c;
    yield (2,c);
  if n > primalitytestlimit and isprime(n) :
    yield (n,1);
    return;
  d = oplist(maxfactor);
  if not n&(n+1) :
    if n == 1 : return;
    e = bit_length(n);    # 2**e-1
    if isprime(e) :
      d = xrange(2*e+1,maxfactor,2*e) if maxfactor else count(2*e+1,2*e);
    else :
      f = tuple(factor(e));
      g = [];
      for q,k in f :
        if len(f) == 1 : k-=1;
        x = (1<<(q**k))-1;
        g.append(x);
        n //= x;
      g.append(n);
      for p in fmerge(*map(factor,g)) : yield p;
      return;
  elif not (n-1)&(n-2) :
    e = bit_length(n)-1; # 2**e+1    
    if not e&(e-1) :  # e = 2**k
      d = xrange(4*e+1,maxfactor,4*e) if maxfactor else count(4*e+1,4*e);
    else :
      x = (1<<(1<<(bit_length(e&-e)-1)))+1;
      for p in fmerge(factor(x),factor(n//x)) : yield p;
      return;
  for p in d :
    if p*p > n :
      if n > 1 : yield (n,1);
      return;
    c = 0;
    while not n % p :
      n //= p;
      c += 1;
    if c :
      yield (p,c);
      if n > primalitytestlimit and isprime(n) :
        yield (n,1);
        return;
  if n > 1 : yield (n,1);

def unfactor(q) :
  """Given sequence of (base,exponent) pairs, return product"""
  p = 1;
  for (n,c) in q : p *= n**c;
  return p;

def nufactor(n,maxfactor=None) :
  """Return factorization of n so unfactor returns n"""
  if n <= 0 :
    yield (n and -1,1);
  for x in factor(n,maxfactor) : yield x;    # yield from factor(n,maxfactor)
  
def fmerge(*args) :
  """Merge factor generators into a single one"""
  d = dict();
  for a in args :
    try :
      d[a] = next(a);
    except StopIteration :
      pass;
  while d :
    f = sorted(d.items(),key=lambda x:x[1][0]);
    p,k = f[0][1];
    for i,j in enumerate(f[1:],1) :
      if j[1][0] == p :
        k += j[1][1];
      else:
        break;
    else :
      i = len(f);
    yield (p,k);
    for j in xrange(i) :
      x = f[j][0];
      try :
        d[x] = next(x);
      except StopIteration :
        del d[x];
  return;

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

zits='0123456789abcdefghijklmnopqrstuvwxyz';

def stradix(x,r=16,n=0) :
  """Return a string representing integer x in radix r
     use alphanumeric zits if r < 37, else use dot-separated decimal zits
     if length of string is less than n, pad on left with 0s to length n"""
  a = [];
  while True :
    a.append(x%r);
    x //= r;
    n -= 1;
    if n<=0 and not x: break;
  a.reverse();
  if r > 36 :
    return '.'.join(map(lambda x:'%d'%(x),a));
  return ''.join(map(lambda x: zits[x],a));

def radstix(s,r=None) :
  """Return an integer represented by the string
     If r is not specified, the string must be of the form
       radix_------- where radix is a 1-or-more-digit base ten number and
       each - is an alphanumeric zit; but if radix is > 36, then
       radix_-.-.-.- where each - is a 1-or-more-digit base ten number;
     If r is specified, it is used as the radix, and
     'radix_' may be omitted but is ignored if present"""
  a = s.split('_');
  if r is None :
    if len(a) != 2 :
      raise ValueError('incorrect format');
    r = int(a[0]);
    a = a[1];
  else :
    if not 1 <= len(a) <= 2 :
      raise ValueError('incorrect format');
    a = a[-1];
  if r < 2 :
    raise ValueError('radix must be at least 2');
  x = 0;
  if r > 36 :
    for z in map(int,a.split('.')) :
      if not 0 <= z < r : raise ValueError('non zit encountered');
      x = r*x+z;
  else :
    for c in a :
      try :
        z = zits.index(c);
      except ValueError :
        raise ValueError('non zit encountered');
      x = r*x+z;
  return x;

def __init__(self,x) :
  """Create a finite field element given its polynomial representation, x
The polynomial can be represented as
  a callable, whose value at p gives one of the following
  an integer with absolute value < p**n :
    if nonnegative, x is the value of the polynomial at p
    if negative, -x is the representation of the negative of the field element
  if p <= 36, a string of at most n zits, each having a value < p;
    these values are the polynomial coefficients, ending with the constant;
    the string is stripped and converted to lower case before evaluation;
    zit values are their positions in '0123456789abcdefghijklmnopqrstuvwxyz'
  an iterable of integers, each with absolute value < p
    these (mod p) are the polynomial coefficients, ending with the constant
    the polynomial evaluated at p must be < p**n
Instance variables:
  _p: the characterisitic of the field (inherited from the type)
  _n: the degree of the polynomial modulus (inherited from the type)
  _x: the polynomial representation, evaluated at x=p"""
  p = self._p;
  n = self._n;
  q = self._q;
  try :
    x = x(p);
  except Exception :
    pass;
  if isint(x) :
    if -q < x < q :
      if x < 0 :
        if p == 2 :
          x = -x;
        elif x > -p :
          x += p;
        else :
          x = -x;
          a = [];
          while x :
            a.append(-x%p);
            x //= p;
          for c in reversed(a) :
            x *= p;
            x += c;
      self._x = x;
    else :
      raise ValueError('absolute value must be < %d'%(q));
  elif isstr(x) :
    if p > 36 :    # string not acceptable if p > 36
      raise TypeError('string not acceptable for p > 36');
    s = x.strip().lower();
    x = 0;
    for c in s :
      try :
        x = x*p + zits[:p].index(c);    # will raise ValueError if illegal
      except ValueError :
        raise ValueError('zits in string must be in "%s"'%(zits[:p]));
      if x > q :
        raise ValueError('value must be < %d'%(q));
    self._x = x;
  elif isffield(type(x)) :
    if x in type(self) :
      self._x = x._x;
    else :
      raise TypeError('ffield element must be in field');
  else :
    try :
      c = iter(x);
    except Exception :
      raise TypeError('uninterpretable arg');
    x = 0;
    for i in c :
      if not isint(i) :
        raise TypeError('iterable elements must be integers');
      if not -p < i < p :
        raise ValueError('absolute value of iterable elements must be < %d)'%(p));
      x *= p
      x += i%p;
      if x >= q :
        raise ValueError('value must be < %d'%(q));
    self._x = x;

@property
def element(self) :
  """the field element's polynomial representation evaluated at p"""
  return self._x;

@property
def elementtuple(self) :
  """the field element's polynomial representation as a tuple"""
  return unpack(self._p,self._x);

@property
def elementpolynomial(self) :
  """the field element's polynomial representation"""
  return pn.polynomial(*unpack(self._p,self._x)).mapcoeffs(self._basefield);

@property
def field_p(self) :
  """the field's characteristic"""
  return self._p;

@property
def field_n(self) :
  """the degree of the field representation's polynomial modulus"""
  return self._n;

@property
def field_q(self) :
  """the size of the field"""
  return self._q;

@property
def field_poly(self) :
  """the field representation's polynomial modulus minus x**n, evaluated at x=p"""
  return self._poly;

@property
def field_fpoly(self) :
  """the field representation's polynomial modulus, evaluated at x=p"""
  return self._p**self._n+self._poly;

@property
def field_tupoly(self) :
  """the field representation's polynomial modulus minus x**n, as a tuple"""
  return self._tupoly[self._nzi:] if self._nzi else ();

@property
def element_order(self) :
  """The multiplicative order of the field element"""
  o = self._q-1;
  if self._x <= 1 :
    return self._x;
  for p in factors(o) :
    while not o%p :
      if (self**(o//p))._x != 1 : break;
      o //= p;
  return o;

@property
def field_ftupoly(self) :
  """the field representation's polynomial modulus, as a tuple"""
  return self._tupoly;

@property
def field_nzi(self) :
  """minus the length of tupoly"""
  return self._nzi;

@property
def field_basefield(self) :
  """the field's base field GF(p)"""
  return self._basefield;

@property
def generates(self) :
  o = self._q-1;
  if self._x <= 1 :
    return self._x==o;
  for p in factors(o) :
    if (self**(o//p))._x == 1 : return False;
  return True;

def __hash__(self) :
  return hash(self._x) if 0 <= self._x < self._p else \
    hash(type(self)) ^ hash(self._x);

def __eq__(self,other) :
  """Test if two elements are equal"""
  x = rint(other);
  if isint(x) :
    return 0 <= x < self._p and self._x == x;
  t = type(x);
  if isffield(t) :
    if t._p != self._p or self._x != x._x : return False;
    while x._x < t._basefield._q < t._q :
      t = t._basefield;
    return t <= type(self);
  return NotImplemented;

def __ne__(self,other) :
  """Test if two elements are unequal"""
  return not self == other;

__le__ = __ge__ = __eq__;
__lt__ = __gt__ = lambda x,y:False;

def __bool__(self) :
  return self._x != 0;

__nonzero__ = __bool__

def __int__(self) :
  """Return self._x if < self._p, else raise TypeError"""
  if self._x < self._p :
    return self._x;
  raise TypeError("can't convert %s element to integer"%(type(self)));

def __str__(self) :
  """Return a string representing the polynomial representation of the finite field element
If n = 1, return the value as a decimal integer, the polynomial evaluated at x=p
Otherwise, return the coefficients in sequence ending with the constant term;
if p <= 36, each coefficient is a zit; else each is a decimal integer, period separated"""
  x = self._x;
  n = self._n;
  p = self._p;
  if n == 1 : return '%d'%(x);
  return stradix(x,p,n);

def __repr__(self) :
  """Return a string representing the polynomial representation of the finite field element
The string begins with the characterisitic of the field as a decimal integer and is followed
by an underscore and the __str__ representation"""
  return str(self._p)+'_'+str(self);

def __add__(self,other) :
  """Return the sum of the two finite field elements; integers are treated mod p"""
  p = self._p;
  n = self._n;
  x = self._x;
  if type(other) != type(self) :
    if isffield(type(other)) and other._p == p :
      if n == 1 :
        return other+x;
      if other._n == 1 :
        other = other._x;
    other = rint(other);
    if isint(other) :
      if p == 2 :
        return type(self)(x^1) if other&1 else self;
      other %= p;
      return type(self)(x-x%p+(x+other)%p) if other else self;
    return NotImplemented;
  y = other._x;
  if not y : return self;
  if p == 2 :
    return type(self)(x^y);
  if n == 1 :
    return type(self)((x+y)%p);
  a = [];
  for i in xrange(n) :
    a.append((x+y)%p);
    x //= p;
    y //= p;
  s = 0;
  for c in reversed(a) :
    s *= p;
    s += c;
  return type(self)(s);

def __pos__(self) :
  """Return the element"""
  return self;

def __neg__(self) :
  """Return the additive inverse of the element"""
  x = self._x;
  if not x : return self;
  p = self._p;
  n = self._n;
  if p == 2 : return self;
  if n == 1 : return type(self)(-x%p);
  a = [];
  while x :
    a.append(-x%p);
    x //= p;
  for c in reversed(a) :
    x *= p;
    x += c;
  return type(self)(x);

def __sub__(self,other) :
  """Return the difference of the two finite field elements; integers are treated mod p"""
  p = self._p;
  n = self._n;
  x = self._x;
  if type(other) != type(self) :
    if isffield(type(other)) and other._p == p :
      if n == 1 :
        return x-other;
      if other._n == 1 :
        other = other._x;
    other = rint(other);
    if isint(other) :
      if p == 2 :
        return type(self)(x^1) if other&1 else self;
      other %= p;
      return type(self)(x-x%p+(x-other)%p) if other else self;
    else :
      return NotImplemented;
  y = other._x;
  if not y : return self;
  if p == 2 : return type(self)(x^y);
  if n == 1 : return type(self)((x-y)%p);
  a = [];
  for i in xrange(n) :
    a.append((x-y)%p);
    x //= p;
    y //= p;
  s = 0;
  for c in reversed(a) :
    s *= p;
    s += c;
  return type(self)(s);

def __rsub__(self,y) :
  """Return the difference of the swapped finite field elements; integers are treated mod p"""
  p = self._p;
  y = rint(y);
  if not isint(y) :
    return NotImplemented;
  if p == 2 :
    return type(self)(self._x^1) if y&1 else self;
  y %= p;
  return type(self)(y)-self if y else -self;

def __div__(self,y) :
  """Return the quotient of the two finite field elements; integers are treated mod p"""
  p = self._p;
  x = self._x;
  n = self._n;
  if type(y) != type(self) :
    if isffield(type(y)) and y._p == p :
      if n == 1 :
        return x/y;
      if y._n == 1 :
        y = y._x;
    y = rint(y);
    if isint(y) :
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
      return type(self)(s);
    else : return NotImplemented;
  yx = y._x;
  if yx < p : return self/yx;
  if p == 2 : return self*type(self)(xm2gcd(self._fpoly,yx)[2]);
  return self*type(self)(pack(p,xmpgcd(p,self._tupoly,unpack(p,yx))[2]));

def __rdiv__(self,y) :    # y/self
  """Return y/self; y must be an integer and is interpreted mod p"""
  p = self._p;
  y = rint(y);
  if not isint(y) :
    return NotImplemented;
  x = self._x;
  if not x : raise ZeroDivisionError;
  y %= p;
  if not y :
    z = 0;
  elif p == 2 :
    return type(self)(xm2gcd(self._fpoly,x)[2]);
  elif x < p :
    z = y*pow(x,p-2,p)%p;
  else :
    z = 0;
    for i in xmpgcd(p,self._tupoly,unpack(p,x))[2] :
      z = p*z+i*y%p;
  return type(self)(z);

def __mul__(self,y) :
  """Return the product of the two finite field elements; integers are treated mod p"""
  p = self._p;
  x = self._x;
  n = self._n;
  if type(y) != type(self) :
    if isffield(type(y)) and y._p == p :
      if n == 1 :
        return y*x;
      if y._n == 1 :
        y = y._x;
    y = rint(y);
    if isint(y) :
      y %= p;
      if not y : return type(self)(0);
      if y == 1 : return self;
      a = [];
      for i in xrange(n) :
        a.append(x*y%p);
        x //= p;
      s = 0;
      for c in reversed(a) :
        s *= p;
        s += c;
      return type(self)(s);
    else : return NotImplemented;
  if n == 1 :
    return type(self)(x*y._x%p);
  if p == 2 :
    y = y._x;
    g = self._poly;
    xy = 0;
    M = 1<<(n-1);
    N = M-1
    m = M;
    while m :
      xy = ((xy&N)<<1)^g if xy&M else xy<<1;
      if y&m : xy ^= x;
      m >>= 1;
    return type(self)(xy);
  return type(self)(pack(p,mpmul(p,unpack(p,x),unpack(p,y._x),self._tupoly)));

def __pow__(self,e) :
  """Raise the finite field element to the specified power mod p**n-1, 0**0=0"""
  e = rint(e);
  if not isint(e) :
    raise TypeError('power must be integer');
  x = self._x;
  if x <= 1 :
    if x or e > 0 : return self;
    if e : raise ZeroDivisionError;
    return self+1;
  p = self._p;
  n = self._n;
  o = self._q-1;
  e %= o;
  if e == 0:
    x = 1;
  elif e == 1 :
    return self;
  elif x < p :
    x = pow(x,e,p);
  elif o-e <= o//8 :
    return 1/self**(o-e);
  elif p == 2 :
    g = self._poly;
    f = self._q | g;
    M = 1<<(n-1);
    N = M-1;
    n = 1<<(bit_length(e)-2);
    b = x;
    while n :
      z = m2sq(x,f);   # z = x*x mod g
      if e&n :
        x = 0;    # compute x = z*b mod g ...
        m = M;
        while m:
          x = ((x&N)<<1)^g if x&M else x<<1;
          if b&m : x ^= z;
          m >>= 1;
      else :
        x = z;
      n >>= 1;
  else :
    x = pack(p,mppow(p,unpack(p,x),e,self._tupoly));
  return type(self)(x);

def _log(self,base=None,alt=False) :
  """Return the discrete log base base (default: least generator) of self
     if alt, values are signed; always searched by increasing magnitude"""
  x = self._x;
  if x : 
    if base is None :
      base = type(self).generator;
    elif not base :
      raise ValueError('bad base');
    q,r = divmod(base.order,self.order);
    if not r :
      if alt :
        for i,g in enumerate(type(self).iterpow(base**q,alt),1) :
          if g._x == x : return (-(i>>1) if i&1 else (i>>1))*q;
      else :
        for i,g in enumerate(type(self).iterpow(base**q)) :
          if g._x == x : return i*q;
  raise ValueError('not in multiplicative group');  

def _vector(x) :
  """A generator of the coefficients of the polynomial representation"""
  p = x._p;
  n = x._n;
  x = x._x;
  for _ in xrange(n) :
    yield x%p;
    x //= p;

def minpolynomial(self,m=1) :
  """Return, as a polynomial with coeffs in the subfield GF(self._p**m),
the minimal polynomial of self over the subfield.
Raise an exception if m does not divide self._n."""
  return pn.polynomial(*minpoly(self,m));

def minpoly(self,m=1) :
  """Return, as a tuple of elements of the subfield GF(self._p**m),
the coefficients, constant term last, of the minimal polynomial of self
over the subfield. Raise an exception if m does not divide self._n."""
  n = self._n;
  if m <= 0 or n%m : raise ValueError('m must divide self._n');
  G = type(self);
  o = self.order;
  p = self._p;
  G1 = G(1);
  O = p**m-1;    # order of subfield
  if not O%(o or 1) :    # already in subfield
    return (G1,-self);
  d = 1;    # calculate degree of minpoly...
  while (p**(m*d)-1)%o :    # order of element must divide order of subfield
    d += 1;
  if m > 1 :
    # brute force algorithm...
    # ceil(ceil(log(o+1,p))/m) is min possible degree of minpoly
    # n/m is the max possible degree
    G0 = G(0);
    P = [G0]*(n//m) + [G1];    # coeffs of 1, x, x**2, x**3, ... x**(n/m)
    for i in xrange(p,G._q) :  # find generator of superfield of subfield
      g = G(i);
      if not g.order % O: break;
    g **= g.order // O;   # generator of subfield
    P[d] = G1;
    while True :
      # evaluate P(self)
      v = G0;
      for i in xrange(d,0,-1) :
        v = (v+P[i])*self;
      if not O%(v.order or 1) :    # evaluates to element of subfield
        P[0] = -v;
        return tuple(P[d::-1]);
      # try next
      for i in xrange(1,d+1) :
        if P[i] :
          if P[i] == G1 :
            P[i] = G0;
          else :
            P[i] *= g;
            break;
        else:
          P[i] = g;
          break;
      else :
        # d += 1;    # should never happen
        # P[d] = G1;
        raise ValueError('Math failure');
  # get minpoly over GF(p) ...
  X = [];
  x = G1;
  for i in xrange(d) :
    X.append(tuple(map(G,_vector(x))));
    x *= self;
  v = list(_vector(x));    # self**d
  M = matrix(n,d,list(chain.from_iterable(X))).T;
  if n > d :
    for c in reversed(xrange(n)) :  # eliminate redundant columns from M and v
      N = matrix(M);
      del N[:,c];
      if N.rank == d :
        M = N;
        del v[c];
        if len(v) == d : break;
  v = map(G,v);
  return (G(1),)+tuple(-(v*M.inverse))[::-1];

def _create(p,n,poly,x=None) :
  """Return an ffield instance or, if x present, an instance of an ffield instance"""
  F = ffield(p,n,poly);
  return F if x is None else F(x);

def __reduce__(self) :
  """Return a tuple for pickling"""
  return (_create,type(self).id+(self._x,));

_ffield = {}; # (p,n,poly) -> ffield

class ffield(type) :
  """Class to create finite field class for GF(p**n)
Field elements are represented as polynomials over GF(p) with degree < n.
Arithmetic is done modulo a specified irreducible monic polynomial of degree n.
That polynomial modulus is represented as a tuple of coefficients, length <= n,
constant term last; the coefficient of x**n is elided and assumed to be 1 while
immediately following zero coefficients may be elided as well.
The polynomial is also stored as its value at x=p, again without the x**n term.
The polynomial modulus can be specified in either of those ways.
Instance variables (treat as read-only!):
  _p: characteristic (a prime)
  _n: dimension (giving the field p**n elements)
  _q: size of the field (p**n)
  _tupoly: the unelided polynomial modulus as a tuple with first element 1
  _poly: an integer giving the value of the elided polynomial at x = _p
  _fpoly: an integer giving the value of the polynomial modulus at x = _p
  _nzi: minus the length of the tuple representing the elided polynomial modulus
  _basefield: ffield(_p)
Methods: __new__, __init__, __hash__, __eq__, __ne__, __lt__, __le__, __ge__, __gt__,
         __len__, __iter__, __getitem__,  __contains__, iterpow, __reduce__
Descriptors: p, n, q, poly, fpoly, tupoly, ftupoly, id,
             polynomial [modulus of field], basefield,
             order [of field-{0}], generator [of field-{0}]

Signatures:
  ffield(q) : q = p**n, a prime power; use least irreducible polynomial
  ffield(q,n,poly) : q, a prime; n, a positive int; poly, a la tupoly or poly
  ffield(q,n) : q, a prime; n, a positive int; use least irreducible polynomial
  ffield(q,poly) : q, a prime power; poly, a la tupoly or poly
  Note: if poly is specified and not poly, use least irreducible polynomial
   unless p==2 in which case use least irreducible polynomial with fewest 1s

Each instance of the created type is an element of the finite field:
Instance variable (treat as read-only!):
  _x: the value at _p of the polynomial representing the element

Methods: __init__, __hash__, __repr__, __str__, __int__,
         __pos__, __neg__,
         __bool__, __nonzero__, __eq__, __ne__, __lt__, __gt__, __le__, __ge__
         __add__, __radd__, __sub__, __rsub__,
         __mul__, __rmul__, __div__, __rdiv__, __truediv__, __rtruediv__,
         __pow__, log, minpoly, minpolynomial
         __reduce__
Descriptors: p, n, q, poly, fpoly, ftupoly, [field parameters]
             x, tupoly, polynomial, [element representations]
             order [of element], generator [True if element generates]
"""

  def __new__(cls,q,*args,**kwargs) :
    q = primepower(q);
    if not q :
      raise ValueError('Not prime power');
    p,n = q;
    poly = kwargs.pop('poly',None);
    dn = kwargs.pop('n',None);
    if dn != None :
      if n != 1 :
        raise ValueError('n specified for prime power');
      n = dn;
    if len(kwargs) :
      raise TypeError('Allowed keywords: n poly')
    if args :
      if len(args) == 1 :
        if (dn or n != 1) and poly != None :
          raise TypeError('too many arguments');
        x = args[0]
        if n == 1 and isint(x) and x :
          n = x;
        elif poly == None :
          poly = x;
        else :
          raise TypeError('too many arguments');
      elif len(args) == 2 :
        if n != 1 or poly != None :
          raise TypeError('too many arguments');
        n,poly = args;
      else :
        raise TypeError('too many arguments');
    if  n < 1 or not isint(n) :
      raise ValueError('Bad power');
    q = p**n;
    if not poly and n > 1:    # pick least irreducible poly
      if p != 2 :
        d = p if (p-1)%product(factors(n),1 if n&3 else 2) else 0;
        for poly in xrange(1+d+q,q+q) :
          if isirreducible(unpack(p,poly)[1:],p) : break;
        poly -= q;
      elif poly == None :
        for poly in xrange(3,q,2) :
          if isirreducible2(poly|q) : break;
      else :    # with fewest possible bits
        poly = 3;    # first, special case 3 bits, for speed
        for _ in xrange(n>>1) :
          if isirreducible2(q|poly) :
            break;
          poly = (poly<<1)-1;
        else :    # if no irreducibles with 3 bits, try bigger odds
          q1 = q|1;
          hq = q>>1;
          for b in xrange(3,n,2) :    # number of inner bits
            hpoly = (1<<b)-1;    # inner bits
            while hpoly < hq :
              poly = q1|(hpoly<<1);    # only try if poly <= bit_reverse(poly)
              if poly <= bit_reverse(poly) and isirreducible2(poly) :
                poly -= q;
                break;
              hpoly = bump_bits(hpoly);
            else :
              continue; 
            break;
    poly = poly or 0;
    if isint(poly) :
      if not 0 <= poly < q : raise ValueError('Bad poly');
    elif isinstance(poly,tuple) and len(poly) <= n :
      tupoly = poly;
      poly = 0;
      for c in tupoly :
        if not (isint(c) and 0 <= c < p) :
          raise ValueError('Bad poly');
        poly = p*poly + c;
    else : raise ValueError('Bad poly');
    tupoly = unpack(p,poly);
    _nzi = -len(tupoly);
    _tupoly = (1,)+(n+_nzi)*(0,)+tupoly;
    if not isirreducible(_tupoly[1:],p) :
      raise ValueError('Composite poly');
    id = (p,n,poly);
    try :
      return _ffield[id];
    except Exception :
      pass;
    d = dict(_p=p, _n=n, _q=q, _poly=poly, _tupoly=_tupoly, _nzi=_nzi,
             _fpoly=q+poly, p=field_p, n=field_n, q=field_q,
             poly=field_poly, fpoly=field_fpoly, ftupoly=field_ftupoly,
             x=element, tupoly=elementtuple, polynomial=elementpolynomial,
             minpoly=minpoly, minpolynomial=minpolynomial,
             order=element_order,
             generator=generates,
             __init__=__init__,
             __repr__=__repr__,
             __str__=__str__,
             __int__=__int__,
             __hash__=__hash__,
             __eq__=__eq__,
             __ne__=__ne__,
             __lt__=__lt__,
             __le__=__le__,
             __gt__=__gt__,
             __ge__=__ge__,
             __bool__ = __bool__,
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
             log = _log,
             __reduce__=__reduce__,
            );

    name = ('GF%d'%(p) if n == 1 and not tupoly else
            'GF%d_%s'%(p,zits[poly] if p <= 36 else str(poly)) if n == 1 else
            'GF%d_%d_%s'%(p,n,''.join([zits[c] for c in tupoly])) if p <= 36 else
            'GF%d_%d_%s'%(p,n,'_'.join(['%d'%(c) for c in tupoly])));
    _ffield[id] = f = type.__new__(cls,name,(),d);
    f._basefield = f if f._n == 1 else ffield(f._p);
    return f;

  def __init__(self,q,*args,**kwargs) :
    return;

  def __reduce__(self) :
    """Return a tuple for pickling"""
    return (_create,self.id);

  def __hash__(self) :
    return hash(type(self))^hash(self.id);

  def __eq__(self,other) :
    return self is other;
  
  def __ne__(self,other) :
    return not self is other;

  def __le__(self,other) :
    if isinstance(other,ffield) :
      return self is other or self is other._basefield;
    return NotImplemented;

  def __ge__(self,other) :
    return other <= self;

  def __lt__(self,other) :
    if isinstance(other,ffield) :
      return not self is other and self is other._basefield;
    return NotImplemented;

  def __gt__(self,other) :
    return other < self;

  def __len__(self) :
    """Return p**n, the size of the field"""
    return self._q;

  def __iter__(self) :
    """Return an iterator for the elements of the field"""
    return (self(x) for x in xrange(self._q));

  def __getitem__(self,key) :
    """Return tuple(self)[key]"""
    if isint(key) :
      q = self._q;
      if -q <= key < q :
        return self(key%q);
      raise IndexError('index out of range');
    elif isinstance(key,slice) :
      return tuple(self(i) for i in range(*key.indices(self._q)));
    raise IndexError('index must be integer or slice');

  def __contains__(self,x) :
    """Return True iff x is an element of the field"""
    return (isinstance(x,self) or isint(rint(x)) and abs(x) < self._p or
            isffield(type(x)) and type(x)>self and x._x < self._q);

  def iterpow(self,x=0,alt=False) :
    """Return an iterator of the powers of x, or powers of smallest generator
       power sequence: 0,1,2,..., or, if alt, 0,1,-1,2,-2,..."""
    if not x :
      x = self.generator;
    if alt :
      def g(f) :
        e = x;
        y = 1/x;
        while True :
          yield f;
          if e._x == f._x : break;
          yield e;
          e *= x;
          if e._x == f._x : break;
          f *= y;
    else :
      def g(e) :
        while True :
          yield e;
          e *= x;
          if e._x <= 1 : break;
    return g(self(1));

  p = field_p;
  n = field_n;
  q = field_q;
  poly = field_poly;
  fpoly = field_fpoly;
  tupoly = field_tupoly;
  ftupoly = field_ftupoly;
  basefield = field_basefield;

  @property
  def polynomial(self) :
    """the polynomial modulus"""
    return pn.polynomial(*self._tupoly).mapcoeffs(self._basefield);

  @property
  def order(self) :
    """p**n-1, the multiplicative order of the field"""
    return self._q-1;

  @property
  def generator(self) :
    """the "smallest" generator of the field"""
    try :
      return self.__generator;
    except AttributeError :
      for g in self :
        if g.generator :
          self.__generator = g;
          return g;

  @property
  def id(self) :
    """the ID of the field: (_p,_n,_poly)"""
    return (self._p,self._n,self._poly);

  def foo(self,foo=None) :
    raise AttributeError("type object '%s' has no Attribute 'x'"%(self.__name__));

  x = property(foo,foo,foo);
  del foo;

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
  return tuple(fg) if not m else mpmod(p,fg,m);

def lstrip(f) :
  for i,x in enumerate(f) :
    if x : return f[i:] if i else f;
  return ();

def mpadd(p,f,g) :
  """Return the sum of f and g, polynomials over GF(p)"""
  f = lstrip(f);
  g = lstrip(g);
  lf = len(f);
  lg = len(g);
  if lf < lg : lf,lg,f,g = lg,lf,g,f;
  ld = lf-lg;
  s = list(f);
  for i in xrange(lg) :
    s[ld+i] = (s[ld+i]+g[i])%p;
  return tuple(lstrip(s));

def mpsub(p,f,g) :
  """Return the difference of f and g, polynomials over GF(p)"""
  return mpadd(p,f,mpneg(p,g));

def mpneg(p,f) :
  """Return the additive inverse of f, a polynomial over GF(p)"""
  return tuple(-x%p for x in lstrip(f));

def mpmod(p,f,g) :
  """Return f mod g, polynomials over GF(p)"""
  g = lstrip(g);
  if not g : raise ZeroDivisionError;
  r = list(lstrip(f));
  dr = len(r)-1;
  dg = len(g)-1;
  if dr < dg :
    return tuple(r);
  ig = pow(g[0],p-2,p);
  for i in xrange(dr+1-dg) :
    if r[i] :
      q = r[i]*ig%p;
      for j in xrange(1,dg+1) :
        r[i+j] = (r[i+j]-q*g[j])%p;
  for i in xrange(dr+1-dg,dr+1) :
    if r[i] : break;
  else :
    return ();
  return tuple(r[i:]);

def mpdivrem(p,f,g) :
  """Return the quotient and remainder from dividing f by g, polynomials over GF(p)"""
  g = lstrip(g);
  if not g : raise ZeroDivisionError;
  r = list(lstrip(f));
  dr = len(r)-1;
  dg = len(g)-1;
  if dr < dg :
    return (),tuple(r);
  ig = pow(g[0],p-2,p);
  q = [];
  for i in xrange(dr+1-dg) :
    q.append(r[i]*ig%p);
    if q[-1] :
      for j in xrange(1,dg+1) :
        r[i+j] = (r[i+j]-q[-1]*g[j])%p;
  for i in xrange(dr+1-dg,dr+1) :
    if r[i] : break;
  else :
    return tuple(q),();
  return tuple(q),tuple(r[i:]);

def mppow(p,b,e,m=None) :
  """Raise b, a polynomial over GF(p), to the nonnegative integer power e, modulo polynomial m"""
  if not e : return (1,);
  n = 1 << (bit_length(e)-1) >> 1;
  x = b;
  while n :
    x = mpmul(p,x,x,m);
    if e&n :
      x = mpmul(p,x,b,m);
    n >>= 1;
  return x;

def mpgcd(p,f,g) :
  """Return the monic gcd of f and g, all polynomials over GF(p)"""
  f = lstrip(f);
  g = lstrip(g);
  while g :
    f,g = g, mpmod(p,f,g);
  return mpmul(p,f,(pow(f[0],p-2,p),)) if f and f[0] != 1 else f;

def xmpgcd(p,f,g) :
  """Return the monic gcd d of f and g, together with u,v such that d=uf+vg,
all polynomials over GF(p); note that g**-1 mod f = xmpgcd(p,f,g)[2]"""
  u0,v0,u1,v1 = (1,),(),(),(1,);
  f = lstrip(f);
  g = lstrip(g);
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

def m2neg(a) :
  """Return the additive inverse of a (which is a), a packed GF(2) polynomial"""
  return a;

def m2add(a,b) :
  """Return the sum (same as difference) of a and b, packed GF(2) polynomials"""
  return a^b;

m2sub = m2add;

def m2mul(a,b,m=0) :
  """Return the product of a and b, packed GF(2) polynomials, mod m"""
  if not a or not b : return 0;
  p = 0;
  if m :
    M = 1<<(bit_length(m)-1);    # hi order bit of m
    g = M^m;
    M >>= 1;
    N = M-1;
    m = M;
    while m :
      p = ((p&N)<<1)^g if p&M else p<<1;
      if b&m : p ^= a;
      m >>= 1;
    return p;
  while b :
    if b&1 : p ^= a;
    b >>= 1;
    a <<= 1;
  return p;

def m2sq(a,m=0) :
  """Return the square of a, a packed GF(2) polynomial, mod m"""
  p = int(bin(a)[2:],4);
  return m2mod(p,m) if m else p;

def m2mod(a,b) :
  """Return a mod b, packed GF(2) polynomials"""
  if not b : raise ZeroDivisionError;
  lb = bit_length(b);
  while True :
    la = bit_length(a);
    if la < lb : break;
    d = la-lb;
    a ^= b<<d;
  return a;

def m2divrem(a,b) :
  """Return the quotient and remainder from dividing a by b, packed GF(2) polynomials"""
  if not b : raise ZeroDivisionError;
  c = 0;
  lb = bit_length(b);
  while True :
    la = bit_length(a);
    if la < lb : break;
    d = la-lb;
    a ^= b<<d;
    c |= 1<<d;
  return c,a;

def m2gcd(a,b) :
  """Return the gcd of a and b, packed GF(2) polynomials"""
  while b :
    a,b = b,m2mod(a,b);
  return a;

def xm2gcd(a,b) :
  """Return the gcd of a and b, together with u,v such that d=uf+vg,
all packed GF(2) polynomials; not that b**-1 mod a = xm2gcd(a,b)[2]"""
  u0,v0,u1,v1 = 1,0,0,1;
  while b :
    q,r = m2divrem(a,b);
    a,b = b,r;
    u0,v0,u1,v1 = u1,v1,u0^m2mul(q,u1),v0^m2mul(q,v1);
  return a,u0,v0;

def m2pow(b,e,m=0) :
  """Raise b, a packed GF(2) polynomial, to the nonnegative integer power e, mod m"""
  if not e : return 1;
  n = 1 << (bit_length(e)-1);
  x = b;
  n >>= 1;
  while n :
    x = m2sq(x,m);
    if e&n :
      x = m2mul(x,b,m);
    n >>= 1;
  return x;

def isirreducible2(p,k=1) :
  """Return True iff p, a packed GF(2) polynomial, is irreducible over GF(2**k)"""
  n = bit_length(p)-1;
  if n <= 1 : return n==1;
  if not (p&1 and bit_count(p)&1) : return False;
  for r in factors(n) :
    if m2gcd(p,m2pow(2,1<<(n//r*k),p)^2) != 1 : return False;
  return not m2mod(m2pow(2,1<<(n*k),p)^2,p);

def isprimitive2(g) :
  """Return True iff packed GF(2) irreducible polynomial g is primitive"""
  if not g&1 : return False;
  n = bit_length(g)-1;
  o = (1<<n)-1;
  # simple algorithm:
  # for f in factors(o) :
  #   d = (1<<(o//f))|1;
  #   if not m2mod(d,g) : return False;
  #  return True;
  # this instead tests all factors at once and with fewer bits:
  for f in factors(o) :    # if o == 1, there are no factors; x+1 is primitive
    if f==o : break;    # o is prime; g is primitive
    d = 0;
    k = n+1;
    c = o//f-n;
    while c > 0:
      d = ((d<<k)|((1<<k)-1))^g;
      if not d : return False;    # g divides x**m-1 for m < 2**n-1
      k = n+1-bit_length(d);
      c -= k;
    break;    # we've tried the smallest factor, so all of them in passing
  return True;

"""The Conway polynomial for q = p^n is the "least" degree n primitive GF(p) polynomial
g_{q} such that if n/m is a prime, g_{q}(x) | g_{p^m}(x^((p^n-1)/(p^m-1))}.
The ordering of polynomials x^n - a_{n-1}x^(n-1) + a_{n-2}x^(n-2) ... (-1)^n a_0
is lexicographically by a_{n-1} a_{n-2} ... a_0."""

_cpdict = {};    # q -> packed Conway polynomial for GF(q) with leading term elided

def conwaypoly(q) :
  """Return the Conway polynomial for GF(q) as a packed GF(p) polynomial,
  where q = p**n, with the coefficient of x**n elided"""
  try :
    return _cpdict[q];
  except Exception :
    pass;
  try :
    p,n = primepower(q);
  except Exception :
    raise ValueError('Not prime power');
  if p == 2 :
    for g in xrange(1,q,2) :
      gq = g|q;
      if isirreducible2(gq) and isprimitive2(gq) :
        for f in factors(n) :
          m = n//f;
          r = 1<<m;
          d = (q-1)//(r-1);
          c = conwaypoly(r);
          xd = m2pow(2,d,gq);
          b = 1<<bit_length(c)>>2;
          a = 1;
          while b :
            a = m2mod(m2mul(a,xd),gq);
            if b&c : a ^= 1;
            b >>= 1;
          if m2pow(2,d*m,gq)^a : break;
        else :
          _cpdict[q] = g;
          return g;
  else :
    for g in irreducibleg(p,n) :
      # modify g by negating alternate terms
      g = tuple(-g[i]%p if i&1 else g[i] for i in xrange(n+1));
      if not isprimitive(g[1:],p) : continue;
      x = (1,0);
      for f in factors(n) :
        m = n//f;
        r = p**m;
        d = (q-1)//(r-1);
        c = unpack(p,conwaypoly(r));
        xd = mppow(p,x,d,g);
        s = [];
        for a in c :
          s = mpadd(p,mpmod(p,mpmul(p,s,xd),g),(a,));
        if mpadd(p,mppow(p,x,d*m,g),s) : break;
      else :
        _cpdict[q] = c = pack(p,g[1:]);
        return c;
  raise SystemError('Did not find Conway polynomial');

def mu(n) :
  """Return the Mobius function of n"""
  if not isint(n) or n < 1 :
    raise ValueError('n must be a positive integer');
  if n <= 1 :
    return 1;
  m = 1;
  if not n&1 :
    if not n&2 : return 0;
    n >>= 1;
    m = -1;
  if n > primalitytestlimit and isprime(n) : return -m;
  p = 3;
  while n > 1 :
    if p*p > n :
      return -m;
    if not n % p :
      n //= p;
      if not n % p : return 0;
      m = -m;
      if n > primalitytestlimit and isprime(n) : return -m;
    p += 2;
  return m;

def irreducible_count(q,n) :
  """Return the number of monic irreducible degree n polynomials over GF(q)"""
  if not primepower(q) : raise ValueError('q must be a power of a prime');
  s = 0;
  for d in xrange(1,n+1) :
    if not n%d :
      s += q**d * mu(n//d);
  return s//n;

def irreducibles(q,n) :
  """Return a tuple of all monic irreducible degree n polynomials over GF(q)
  whose coefficients lie in GF(p), where q = p**k, as tuples of integers.
  All monic irreducible degree n polynomials over GF(q): poly.irreducibles"""
  return tuple(irreducibleg(q,n));

def irreducibleg(q,n) :
  """Generate lexicographically as tuples of nonnegative integers < p,
  all monic irreducible degree n polynomials over GF(q)
  whose coefficients lie in GF(p), where q = p**k.
  All monic irreducible degree n polynomials over GF(q): poly.irreducibleg"""
  p = primepower(q);
  if not p : raise ValueError('q must be a power of a prime');
  p = p[0];
  for i in xrange(p**n) :
    poly = [];
    j = i;
    for k in xrange(n) :
      poly.append(j%p);
      j //= p;
    poly = tuple(reversed(poly));
    if isirreducible(poly,q) : yield (1,)+poly;

def phi(n) :
  """Return the Euler totient function of n"""
  if not n : return 0;
  p = 1;
  for n,c in factor(n) :
    p *= (n-1)*n**(c-1);
  return p;

def sigma(n) :
  """Return the sum of the positive divisors of n"""
  if not n : return 0;
  p = 1;
  for n,c in factor(n) :
    p *= (n**(c+1)-1)//(n-1);
  return p;

def lam(n) :
  """Return the reduced totient function of n"""
  if not n : return 0;
  p = 1;
  for n,c in factor(n) :
    x = (n-1)*n**(c-1) if n&1 or c < 3 else 1<<(c-2);
    p *= x//gcd(x,p);
  return p;

def numdivisors(n) :
  """Return the number of positive divisors of n"""
  if not n: return 0;
  p = 1;
  for n,c in factor(n) :
    p *= c+1;
  return p;

def divisors(n) :
  """Return the positive divisors of n as a generator"""
  if not n : return;
  yield 1;
  f = [];
  t = [];
  for a in factor(n) :
    f.append(a);
    t.append(1);
    z = 0;
    while z < len(f) :
      p = 1;
      for i,x in enumerate(f) :
        p *= x[0]**t[i];
      yield p;
      while z < len(f) :
        t[z] += 1;
        if t[z] <= f[z][1] :
          z = 0;
          break;
        t[z] = 0;
        z += 1;

def lcm(x,y) :
  """Return the [positive] least common multiple of x and y"""
  return abs(x//(gcd(x,y) or 1)*y);

def lcma(*args) :
  """Return the [positive] least common multiple of all the arguments"""
  m = 1;
  for a in args :
    try :
      m *= a//(gcd(m,a) or 1);
    except Exception :
      for i in a :
        m *= i//(gcd(m,i) or 1);
  return abs(m);

def gcda(*args) :
  """Return the [nonnegative] greatest common divisor of all the arguments"""
  d = 0;
  for a in args :
    try :
      d = gcd(d,a);
    except Exception :
      for i in a :
        d = gcd(d,i);
  return d;

def getorder(n) :
  """Return a method that returns the multiplicative order of an element mod n
method attributes: modulus = n, maxorder = lam(n)"""
  l = lam(n);
  f = tuple(factors(l));
  def order(x) :
    x = x%n;
    if gcd(x,n) != 1 : return 0;
    o = l;
    for p in f :
      while not o%p :
        if pow(x,o//p,n) != 1 : break;
        o //= p;
    return o;
  order.modulus = n;
  order.maxorder = l;
  return order;

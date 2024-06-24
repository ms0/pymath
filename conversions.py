from __future__ import division

import sys

if sys.version_info>(3,) :
  unicode = str;
  long = int;
  isint = lambda x: isinstance(x,int);
  isreal = lambda x: isinstance(x,(int,float));
  iscomplex = lambda x: isinstance(x,(int,float,complex));
  isstr = lambda x: isinstance(x,str);
  iteritems = lambda x: x.items();
  lmap = lambda *x: list(map(*x));
  xrange = range;
  range = lambda *x: list(xrange(*x));
else :
  long = long;
  isint = lambda x: isinstance(x,(int,long));
  isreal = lambda x: isinstance(x,(int,long,float));
  iscomplex = lambda x: isinstance(x,(int,long,float,complex));
  isstr = lambda x: isinstance(x,(str,unicode));
  iteritems = lambda x: x.iteritems();
  lmap = map;
  _range = range;
  range = _range;
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

def intfloat(x) :
  """Return int(x) if same as x, else float(x)"""
  y = int(x);
  return y if y==x else float(x);

try :
  from math import gcd
except Exception :
  def gcd(x,y) :
    """Return the [nonnegative] greatest common divisor of x and y"""
    while y :
      x,y = y, x%y;
    return abs(x);

try :
  from math import lcm
except Exception :
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

try :
  int.bit_length;
  bit_length = lambda n : n.bit_length();
except Exception :
  from math import log
  def bit_length(n) :
    n = abs(n);
    b = 0;
    while n :
      try :
        l = int(log(n,2));
        while n >> l : l += 1;
      except OverflowError :
        l = sys.float_info.max_exp-1;
      b += l
      n >>= l;
    return b;

def isffield(t) :
  """Return True iff t is a finite field"""
  if not isinstance(t,type) : return False;
  try :
    t._basefield;
    return isint(t._q);
  except Exception :
    return False;

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

def pack(p,a) :
  """Return the evaluation at x=p of a, an iterable of coefficients, constant last"""
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

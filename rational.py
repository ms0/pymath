# class rational, implementing Q, the field of rational numbers

from __future__ import division
from math import floor, log

inf = float('inf');

def sgn(x) :
  """Return the sign of x as an integer: -1, 0, or +1"""
  return -1 if x < 0 else 1 if x else 0;

def gcd(x,y) :
  """Return the [nonnegative] greatest common divisor of x and y"""
  while y :
    x,y = y, x%y;
  return abs(x);

def root(a,n) :
  """Return the nth root of a, where a and n are positive integers"""
  l = log(a,2)/n;
  try :
    r = int(round(2**l));
  except :    # too big
    il = int(l)-52;
    fl = l - il;
    r = int(round(2**fl))<<52;
  while True :
    if r**n == a : return r;
    ro = r;
    r = ((n-1)*r + a//r**(n-1))//n;
    if -1 <= ro-r <= 1 :
      return ro if abs(a-ro**n) < abs(a-r**n) else r;
    

class rational :
  """Rational number class
Instance variables:
  a, the numerator, an integer
  b, the denominator, a positive integer
  Note that gcd(a,b) == 1.
Methods:
  __init__, __hash__, __repr__, __str__, __nonzero__,
  __eq__, __ne__, __lt__, __le__, __ge__, __gt__,
  __pos__, __neg__, __abs__,
  __int__, __float__, __round__, __ceil__, __floor__, __trunc__,
  __add__, __radd__, __sub__, __rsub__, __mul__, __rmul__, __div__, __rdiv__,
  __truediv__, __rtruediv__, __floordiv__, __rfloordiv__, __mod__, __rmod__,
  __divmod__, __rdivmod__, __lshift__, __rshift__
  __pow__, __rpow__, log, cf"""

  def __init__(self,a,b=1) :
    """Create a rational number equal to a/b; attempting b=0 raises ZeroDivisionError
If a is a float (and b==1), return the simplest possible rational
If a is a nonempty list or tuple of integers (and b==1),
 they are interpreted as the terms of a regular continued fraction"""
    if not isinstance(a,(int,long)) or not isinstance(b,(int,long)) :
      if b == 1 :
        if isinstance(a,float) :
          x = a;
          m0,m1,n0,n1 = 0,1,1,0;
          for i in range(64) :
            ix = floor(x);
            fx = x - ix;        
            iix = int(ix);
            m0,m1,n0,n1 = n0,n1,m0+iix*n0,m1+iix*n1;
            if fx == 0 or n0/n1 == a : break;
            x = 1/fx;
          self.a,self.b = int(n0),int(n1);
          return;
        elif a and isinstance(a,(tuple,list)) :
          m0,m1,n0,n1 = 0,1,1,0;
          for i in a :
            if not isinstance(i,(int,long)) : raise TypeError('cf must be integral');
            if i <= 0 and n1 : raise TypeError('cf terms beyond first must be positive');
            m0,m1,n0,n1 = n0,n1,m0+i*n0,m1+i*n1;
          self.a,self.b = int(n0),int(n1);
          return;
      raise TypeError('Numerator and Denominator must be integers');
    if b < 0 : a,b = -a,-b;
    if not b : raise ZeroDivisionError;
    g = gcd(a,b);
    self.a = int(a//g);
    self.b = int(b//g);

  def __str__(self) :
    """Return a string showing the rational number as a fraction or integer"""
    return '%d/%d'%(self.a,self.b) if self.b != 1 else '%d'%(self.a);

  def __repr__(self) :
    """Return a string showing the rational number as it could be input"""
    return 'rational(%d,%d)'%(self.a,self.b) if self.b != 1 else 'rational(%d)'%(self.a);

  def __hash__(self) :
    """Return a hash for the rational number; if an integer, use that integer's hash"""
    if self.b == 1 : return hash(self.a);
    return hash(self.__class__)^hash(str(self));

  def __lt__(self,other) :
    """Return True iff self < other """
    if not isinstance(other,self.__class__) :
      if isinstance(other,(int,long)) :
        return self.a < self.b*other;
      elif isinstance(other,float) :
        return self < rational(other);
      else :
        return False;
    return self.a*other.b < self.b*other.a;

  def __le__(self,other) :
    """Return True iff self <= other"""
    if not isinstance(other,self.__class__) :
      if isinstance(other,(int,long)) :
        return self.a <= self.b*other;
      elif isinstance(other,float) :
        return self <= rational(other);
      else :
        return False;
    return self.a*other.b <= self.b*other.a;

  def __eq__(self,other) :
    """Return True iff self == other"""
    if not isinstance(other,self.__class__) :
      if isinstance(other,(int,long)) :
        return self.a == self.b*other;
      elif isinstance(other,float) :
        return self == rational(other);
      else :
        return False;
    return self.a*other.b == self.b*other.a;

  def __ne__(self,other) :
    """Return True iff self != other"""
    if not isinstance(other,self.__class__) :
      if isinstance(other,(int,long)) :
        return self.a != self.b*other;
      elif isinstance(other,float) :
        return self != rational(other);
      else :
        return True;
    return self.a*other.b != self.b*other.a;

  def __ge__(self,other) :
    """Return True iff self >= other"""
    if not isinstance(other,self.__class__) :
      if isinstance(other,(int,long)) :
        return self.a >= self.b*other;
      elif isinstance(other,float) :
        return self >= rational(other);
      else :
        return False;
    return self.a*other.b >= self.b*other.a;

  def __gt__(self,other) :
    """Return True iff self > other"""
    if not isinstance(other,self.__class__) :
      if isinstance(other,(int,long)) :
        return self.a > self.b*other;
      elif isinstance(other,float) :
        return self > rational(other);
      else :
        return False;
    return self.a*other.b > self.b*other.a;

  def __nonzero__(self) :
    """Return True iff self != 0"""
    return self.a != 0;

  def __pos__(self) :
    """Return self"""
    return self;

  def __neg__(self) :
    """Return -self"""
    return rational(-self.a,self.b) if self.a else self;

  def __abs__(self) :
    """Return |self|"""
    return rational(-self.a,self.b) if self.a < 0 else self;

  def __add__(self,other) :
    """Return the sum of the two numbers"""
    if not isinstance(other,self.__class__) :
      return self+rational(other);
    return rational(self.a*other.b+other.a*self.b,self.b*other.b);

  __radd__ = __add__

  def __sub__(self,other) :
    """Return the difference of the two numbers"""
    if not isinstance(other,self.__class__) :
      return self-rational(other);
    return rational(self.a*other.b-other.a*self.b,self.b*other.b);

  def __rsub__(self,other) :
    """Return the difference of the swapped two numbers"""
    return rational(other)-self;

  def __mul__(self,other) :
    """Return the product of the two numbers"""
    if not isinstance(other,self.__class__) :
      if isinstance(other,(int,long)) :
        return rational(self.a*other,self.b);
      return self*rational(other);
    return rational(self.a*other.a,self.b*other.b);

  __rmul__ = __mul__

  def __truediv__(self,other) :
    """Return the quotient of the two numbers"""
    if not isinstance(other,self.__class__) :
      if isinstance(other,(int,long)) :
        return rational(self.a,other*self.b);
      return self/rational(other);
    return rational(self.a*other.b,self.b*other.a);

  def __rtruediv__(self,other) :
    """Return the inverse quotient of the two numbers"""
    if not isinstance(other,self.__class__) :
      if isinstance(other,(int,long)) :
        return rational(other*self.b,self.a);
      return rational(other)/self;
    return rational(self.b*other.a,self.a*other.b);

  __div__ = __truediv__
  __rdiv__ = __rtruediv__

  def __floordiv__(self,other) :
    """Return the floor of the quotient of the two numbers"""
    if not isinstance(other,self.__class__) :
      if isinstance(other,(int,long)) :
        return rational(self.a//(self.b*other));
      return self//rational(other);
    return rational((self.a*other.b)//(self.b*other.a));

  def __rfloordiv__(self,other) :
    """Return the floor of the inverse quotient of the two numbers"""
    if not isinstance(other,self.__class__) :
      if isinstance(other,(int,long)) :
        return rational((self.b*other)//self.a);
      return rational(other)//self;
    return rational((self.b*other.a)//(self.a*other.b));

  def __mod__(self,other) :
    """Return the remainder from floordiv"""
    return self - self//other*other;

  def __rmod__(self,other) :
    """Return the remainder from rfloordiv"""
    return other - other//self*self;

  def __divmod__(self,other) :
    """Return quotient and remainder"""
    q = self//other;
    return (q, self-q*other);

  def __rdivmod__(self,other) :
    """Return quotient and remainder"""
    q = other//self;
    return (q, other-q*self);

  def __pow__(self,other) :
    """Return a number raised to a power; integer powers give exact answer"""
    if isinstance(other,float) :
      other = rational(other);
    if isinstance(other,rational) and other.b == 1 :
      other = other.a;
    if isinstance(other,(int,long)) :
      if other < 0 :
        if not self.a : raise ZeroDivisionError;
        return rational(self.b**other,self.a**other);
      return rational(self.a**other,self.b**other);
    if not isinstance(other,rational) :
      raise TypeError('exponent must be an integer');
    # rational (but not integral) power
    if other.a < 0 :
      a,b = self.b**-other.a, self.a**-other.a;
    else :
      a,b = self.a**other.a, self.b**other.a;
    # now, take the root
    if a < 0 and not other.b&1 :
      raise ValueError('complex result')    # even root of negative number
    # first see if a and/or b has an integer root
    ra = sgn(a)*root(abs(a),other.b);
    rb = root(b,other.b);
    pa = ra**other.b == a;  # a has an exact root?
    pb = rb**other.b == b;  # b has an exact root
    if pa and pb : return rational(ra,rb);
    if pa and abs(b) > 1 << 28:    # exact result:
      return ra*other.b/((other.b-1)*rb + rational(b,rb**(other.b-1)))
    # return an inexact result :
    if pb and abs(a) > 1 << 28 :
      return ((other.b-1)*ra + rational(a,ra**(other.b-1)))/(rb*other.b);
    logroot = rational(abs(a),b).log(2)/other.b;
    alogroot = abs(logroot);
    ilogroot = int(alogroot);
    flogroot = alogroot-ilogroot;
    r = rational(2**flogroot)*(sgn(a)<<ilogroot);
    if logroot < 0 : r = 1/r;
    x = rational(a,b);
    return ((other.b-1)*r + x/r**(other.b-1))/other.b;

  def __rpow__(self,other) :
    return rational(other)**self;

  def __lshift__(self,other) :
    """Return the product of self and 2**other, for other an integer"""
    return rational(self.a<<other,self.b) if other >= 0 else self>>-other;

  def __rshift__(self,other) :
    """Return the quotient of self and 2**other, for other an integer"""
    return rational(self.a,self.b<<other) if other >= 0 else self<<-other;

  def __float__(self) :
    """Return a floating point approximation to the number"""
    return self.a/self.b;

  def __int__(self) :
    """Return the integer part of the number"""
    return int(-(-self.a//self.b) if self.a < 0 else self.a//self.b);

  __trunc__ = __int__

  def __floor__(self) :
    """Return the floor of the number"""
    return int(self.a//self.b);

  def __ceil__(self) :
    """Return the ceil of the number"""
    return int(-(-self.a//self.b));

  def __round__(self,n) :
    """Return the round of the number"""
    ten2absn = 10**abs(n);
    return ((int((self/ten2absn - half)*ten2absn) if self.a < 0 else
             int(self/ten2absn + half)*ten2absn) if n < 0 else
            -((half - self*ten2absn)//ten2absn) if self.a < 0 else
            (half + self*ten2absn)//ten2absn);

  def log(self,*base) :
    """Return the log of the number as a float"""
    if base and (base[0] <= 0 or base[0] == 1) : raise ValueError('bad base');
    if not self.a : return inf if base and base[0] < 1 else -inf;
    a = self.a;
    b = self.b;
    c = base and base[0];
    if c and c < 1 : a,b,c=b,a,1/c;
    if c and int(c) == c :
      c = int(c);    # try for maximum precision
      la = int(round(log(a,c)));
      lb = int(round(log(b,c)));
      a /= c**la;
      b /= c**lb;
      return (la-lb)+(log(a,c)-log(b,c));
    else :    # non-integral base
      try :
        b/a;    # this might overflow (in which case a/b might be denormalized)
        return log(a/b,*base);    # might overflow
      except :
        return log(a,*base)-log(b,*base); # less precise than the above

  def cf(self) :
    """Return a tuple of the terms of the regular continued fraction for the number"""
    l = [];
    a,b = self.a,self.b;
    while b :
      q = int(a//b);    # turn long into int if possible
      l.append(q);
      a,b = b,int(a-q*b);
    return tuple(l);

half = rational(1,2);

# class rational, implementing Q, the field of rational numbers

from __future__ import division
from math import floor

def sgn(x) :
  """Return the sign of x as an integer: -1, 0, or +1"""
  return x/abs(x) if x else 0;

def gcd(x,y) :
  """Return the [nonnegative] greatest common divisor of x and y"""
  while y :
    x,y = y, x%y;
  return abs(x);

class rational :
  """Rational number class
Instance variables:
  a, the numerator, an integer
  b, the denominator, a positive integer
  Note that gcd(a,b) == 1.
Methods:
  __init__, __hash__, __repr__, __str__, __nonzero__,
  __eq__, __ne__, __lt__, __le__, __ge__, __gt__,
  __pos__, __neg__, __abs__, __int__, __float__,
  __add__, __radd__, __sub__, __rsub__, __mul__, __rmul__, __div__, __rdiv__,
  __truediv__, __rtruediv__, __floordiv__, __rfloordiv__, __mod__, __rmod__,
  __pow__"""

  def __init__(self,a,b=1) :
    """Create a rational number equal to a/b; attempting b=0 raises ZeroDivisionError
If a is a float (and b==1), return the simplest possible rational"""
    if not isinstance(a,(int,long)) or not isinstance(b,(int,long)) :
      if b == 1 and isinstance(a,float) :
        x = a;
        m0,m1,n0,n1 = 0,1,1,0;
        for i in range(64) :
          ix = floor(x);
          fx = x - ix;        
          iix = int(ix);
          m0,m1,n0,n1 = n0,n1,m0+iix*n0,m1+iix*n1;
          if fx == 0 or n0/n1 == a : break;
          x = 1/fx;
        self.a,self.b = n0,n1;
        return;
      raise TypeError('Numerator and Denominator must be integers');
    if b < 0 : a,b = -a,-b;
    if not b : raise ZeroDivisionError;
    g = gcd(a,b);
    self.a = a//g;
    self.b = b//g;

  def __str__(self) :
    """Return a string showing the rational number as a fraction or integer"""
    return '%d/%d'%(self.a,self.b) if self.b != 1 else '%d'%(self.a);

  def __repr__(self) :
    """Return a string showing the rational number as it could be input"""
    return 'rational(%d,%d)'%(self.a,self.b) if self.b != 1 else '%d'%(self.a);

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

  def __pow__(self,other) :
    """Return the number raised to the (integer) power"""
    if not isinstance(other,(int,long)) :
      raise TypeError('exponent must be an integer');
    if other < 0 :
      if not self.a : raise ZeroDivisionError;
      return rational(self.b**other,self.a**other);
    return rational(self.a**other,self.b**other);

  def __float__(self) :
    """Return a floating point approximation to the number"""
    return self.a/self.b;

  def __int__(self) :
    """Return the integer part of the number"""
    return -(-self.a//self.b) if self.a < 0 else self.a//self.b;

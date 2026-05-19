__all__ = ['conic','easeyes','testconic','testconics']

from msmath.rational import *
import tkinter as tk

zero = rational(0)
one = rational(1)

def intersect(l1,l2) :    # return intersection of two lines
  # ax + by = -c   [a b] [x] = [-c]    [x] = __1__ [q -b] [-c] =  __1__ [br-qc]
  # px + qy = -r   [p q] [y]   [-r]    [y]   aq-pb [-p a] [-r]    aq-pb [pc-ar]
  d = l1[0]*l2[1]-l2[0]*l1[1]
  return ((l1[1]*l2[2]-l2[1]*l1[2])/d, (l2[0]*l1[2]-l1[0]*l2[2])/d)

class conic() :
  """Conic section class
Instance variables:
 Always present:
  classification, a string specifying the type of conic section:
    empty, point, line, doubled line, parallel lines, crossing lines,
    circle, ellipse, parabola, hyperbola
  coeffs, coefficients (a,b,c,d,e,f) of the conic's quadratic ax^2+bxy+cy^2+dx+ey+f = 0
    the coefficients are usually normalized to conform to the conic equation
    (x-u)^2 + (y-v)^2 = g^2 (px+qy+r)^2 / (p^2+q^2)
    where (u,v) is the focus and px+qy+r = 0 is the directrix;
    for circles, the conic equation is (x-u)^2 + (y-v)^2 = r^2 where (u,v) is the center
  eccentricity, a scalar
  focus, a 2-tuple (u,v)
  directrix, a 3-tuple (p,q,r) representing the line px+qy+r = 0;
    p^2 + q^2 = 1, except for circles where p = q = 0 and r = radius
 Sometimes present:
  center, a 2-tuple for the center of the conic (not present for parabolas)
  vertex, a 2-tuple for the vertex of a parabola
  axis, a 3-tuple for the axis through the focus (not present for circles)
  asymptotes, a 2-tuple of 3-tuples (only for hyperbolas)
  foci, a 2-tuple of the two foci (but a 1-tuple for parabolas and circles)
  directrices, a 2-tuple of the two directrices
    (but a 1-tuple for parabolas and circles)
  axes, a 2-tuple of the major and minor axes
    (but a 1-tuple for parabolas) (not present for circles)
  ad, a 2-tuple of intersections of the directrices with the axis
    (but a 1-tuple for parabolas) (not present for circles)
  point, a 2-tuple for a degenerate conic that's a single point
  line, a 3-tuple for a degenerate conic that's a single or doubled line
  lines, a 2-tuple of 3-tuples for a degenerate conic that's pair of lines,
     parallel or crossing
 All numbers are represented using the rational class"""

  def __init__(self,*args,**kwargs) :
    """A conic instance can be created in one of two ways:
 by specifying the keyword args eccentricity, focus, and directrix; or
 by specifying the six coefficients a,b,c,d,e,f;
 the directrix (p,q,r) or coefficients (a,b,c,d,e,f) do not need to be normalized,
   any nonzero multiple will do, except for circles (where eccentricity=0)"""
    try :
      u,v = self.focus = tuple(map(rational,kwargs['focus']))
      p,q,r = self.directrix = tuple(map(rational,kwargs['directrix']))
      g = self.eccentricity = rational(kwargs['eccentricity'])
      if g < 0 :
        raise ValueError('eccentricity must be nonnegative')
      gg = g*g
      if not g :
        if p or q :
          raise ValueError('circles cannot have finite directrix')
        s = 1
      else :
        s = g*g/(p*p+q*q)
        if not isfinite(s) :
          raise ValueError('directrix not normalizable')
      a,b,c,d,e,f = \
        self.coeffs = (1-p*p*s, -2*p*q*s, 1-q*q*s, -2*(u+p*r*s), -2*(v+q*r*s), u*u+v*v-r*r*s)
    except KeyError :
      a,b,c,d,e,f = map(rational,args)
      # normalize a through f
      b4 = b*b - 4*a*c
      if b4 :    # ellipse or hyperbola
        s = (a+c)**2/b4 + 1
        t = s*(s-1)
        if t < 0 :
          raise ValueError('no real solutions')
        if b4 < 0 :
          gg = 2*(s+sqrt(t))
          k = (a+c)/(2-gg)
        else :
          pm = sgn(b4*f+a*e*e+c*d*d-b*d*e) or sgn(b)
          gg = 2*(s-sgn(a+c)*pm*sqrt(t))
          if a+c :
            k = (a+c)/(2-gg)
          else :    # gg == 2
            k = pm*sqrt(b4)/2 or 1
        a,b,c,d,e,f = self.coeffs = (a/k,b/k,c/k,d/k,e/k,f/k)
      else :    # parabola
        k = a+c or hypot(d,e) or f or 1
        a,b,c,d,e,f = self.coeffs = (a/k,b/k,c/k,d/k,e/k,f/k)
        gg = 1
      self.eccentricity = g = sqrt(gg)
    ggm1 = gg-1
    p = sqrt(1-a)
    q = -b/2/p if p else sqrt(1-c)
    dpeq = d*p + e*q
    fm = f - (d*d+e*e)/4
    if ggm1 :
      r = (-dpeq + sqrt(dpeq*dpeq+ggm1*fm*4)).real/2/ggm1
      s,t = self.center = ((2*c*d-b*e)/4/ggm1, (2*a*e-b*d)/4/ggm1)
      if ggm1 > 0 :
        if a or c :
          # bb-4ac = 4*ggm1; sqrt(bb-4ac) = 2*sqrt(ggm1)
          m0 = sqrt(ggm1)
          if abs(a) >= abs(c) :
            m1 = (b/2+m0)/a
            m2 = (b/2-m0)/a
            h1 = hypot(1,m1)
            h2 = hypot(1,m2)
            self.asymptotes = ((1/h1,m1/h1,(-s-m1*t)/h1),
                               (1/h2,m2/h2,(-s-m2*t)/h2))
          else :
            m1 = (b/2+m0)/c
            m2 = (b/2-m0)/c
            h1 = hypot(1,m1)
            h2 = hypot(1,m2)
            self.asymptotes = ((m1/h1,1/h1,(-s*m1-t)/h1),
                               (m2/h2,1/h2,(-s*m2-t)/h2))
        else :
          self.asymptotes = ((one,zero,-s),(zero,one,-t))
    else :
      r = fm/dpeq
    u,v = self.focus = (-d/2-p*r,-e/2-q*r)
    h = hypot(p,q) or sgn(r)
    p /= h
    q /= h
    r /= h
    self.directrix = (p,q,r)
    if gg*ggm1 :
      self.foci = (self.focus, (2*s-u,2*t-v))
      self.directrices = (self.directrix,(p,q,-2*p*s-2*q*t-r))
      dx = s-u
      dy = t-v
      h = hypot(dx,dy)
      dx /= h
      dy /= h
      self.axis = (dy,-dx,dx*t-dy*s)    # line through foci
      self.axes = (self.axis,(dx,dy,-dx*s-dy*t))  # + perpendicular thru center
      self.ad = (intersect(self.directrices[0],self.axis),
                 intersect(self.directrices[1],self.axis))
    else :
      self.foci = (self.focus,)
      self.directrices = (self.directrix,)
      if gg :
        h = (p*u+q*v+r)/2
        self.vertex = (u-p*h,v-q*h)
        self.axis = (q,-p,v*p-u*q)
        self.axes = (self.axis,)
        self.ad = (intersect(self.directrix,self.axis),)
    rad = a*e*e+c*d*d+(b*b-4*a*c)*f-b*d*e
    if rad <= 0 :
      if rad :
        self.classification = 'empty'
      elif ggm1 :
        del self.axis
        del self.axes
        if ggm1 < 0 :
          self.classification = 'point'
          self.point = self.center
        else :
          self.classification = 'crossing lines'
          self.lines = self.asymptotes
      elif a or b or c :
        o2 = d*d/4/a if a else e*e/4/c
        p = f-o2
        if p > 0 :
          self.classification = 'empty'
        else :
          m = sqrt(a)
          n = sqrt(c)
          h = sqrt(a+c)
          o = sqrt(o2)
          if p :
            p = sqrt(-p)
            self.classification = 'parallel lines'
            self.lines = ((m/h,n/h,(o+p)/h),(m/h,n/h,(o-p)/h))
          else :
            self.classification = 'doubled line'
            self.line = (m/h,n/h,o/h)
      elif d or e :
        self.classification = 'line'
        self.line = (d,e,f)
      elif f :
        self.classification = 'empty'
      else :
        self.classification = 'plane'
    else :
      if gg :
        if ggm1 :
          if ggm1 < 0 :
            self.classification = 'ellipse'
          else :
            self.classification = 'hyperbola'
        else :
          self.classification = 'parabola'
      else :
        self.classification = 'circle'

  def __repr__(self) :
    return 'conic(%s,%s,%s,%s,%s,%s)'%(self.coeffs)

  def __call__(self,x,y) :
    """Return ax^2+bxy+cy^2+dx+ey+f; 0 iff on curve"""
    a,b,c,d,e,f = self.coeffs
    return a*x*x + b*x*y + c*y*y + d*x + e*y + f

  def translated(self,*args) :
    """Return a new conic translated as specified by x,y args;
if no args, use center coords, or vertex coords if no center"""
    a,b,c,d,e,f = self.coeffs
    if args :
      x,y = args
    else :
      try :
        x,y = self.center
      except Exception :
        try :
          x,y = self.vertex
        except Exception : 
          raise KeyError('Neither center nor vertex exist')
      x,y = -x,-y
    return conic(a,b,c,d-2*a*x-b*y,e-b*x-2*c*y,f+a*x*x+b*x*y+c*y*y-d*x-e*y)

  def draw(self) :  # use sin,cos, or sinh, cosh, or y=ax^2
    """Draw conic with tkinter, centered and scaled but unrotated"""
    # We must translate and scale to fit picture in window
    # For single or doubled line, have it go through origin
    # For crossed lines, have them cross at the origin
    # For circle, use entire window
    # For point, use origin
    # For parabola, place focus at origin, directrix quarter away (512/4 = 128)
    # For ellipse or hyperbola, center at origin,
    #  foci and intersection of axis and directrix inside window
    tkroot = tk.Tk()
    canvas = tk.Canvas(tkroot, width=512, height=512, bg='white')
    canvas.pack()
    drawdict[self.classification.split()[0]](self,canvas)
    tkroot.mainloop()

v2 = sqrt(2)

def tofloat(*args) :
  """Convert rational args to a tuple of floats"""
  return tuple(map(float,args))

def drawtpoint(canvas,point,origin,scale) :
  x,y = tofloat((point[0]-origin[0])*scale,(point[1]-origin[1])*scale)
  canvas.create_oval(255.5+x,255.5-y,256.5+x,256.5-y,fill='gray')

def drawtline(canvas,line,origin,scale) :
  # line: px + qy + r = 0    origin: a,b
  # scaled distance from origin = (pa + qb + r)*scale
  # new line: p,q,(pa+qb+r)*scale ?
  p,q,r = line
  a,b = origin
  r = (r+p*a+q*b)*scale
  canvas.create_line(*tofloat
                     (256*(1+v2*q)-r*p,256*(1+v2*p)+r*q,
                      256*(1-v2*q)-r*p,256*(1-v2*p)+r*q),
                     fill='gray',width=1)

def drawempty(c,canvas) :
  pass

def drawpoint(c,canvas) :
  canvas.create_oval(255.5,255.5,256.5,256.5,fill='black')

def drawline(c,canvas) :
  dx,dy = c.line[1],-c.line[0]
  canvas.create_line(*tofloat
                     (256*(1-v2*dx),256*(1-v2*dy),
                      256*(1+v2*dx),256*(1+v2*dy)),
                     fill='black',width=1)

def drawplines(c,canvas) :
  for i in range(2) :
    dx,dy = c.lines[0][:2]
    canvas.create_line(*tofloat
                       (256*(1-v2*dy)+(2*i-1)*16*dx,256*(1+v2*dx)+(2*i-1)*16*dy,
                        256*(1+v2*dy)+(2*i-1)*16*dx,256*(1-v2*dx)+(2*i-1)*16*dy),
                       fill='black',width=1)

def drawclines(c,canvas) :
  for i in range(2) :
    dx,dy = c.lines[i][1],-c.lines[i][0]
    canvas.create_line(*tofloat
                       (256*(1-v2*dx),256*(1-v2*dy),
                        256*(1+v2*dx),256*(1+v2*dy)),
                       fill='black',width=1)

def drawplane(c,canvas) :
  canvas.create_rectangle(0,0,512,512,fill='black')
  
def drawcircle(c,canvas) :
  drawtpoint(canvas,(0,0),(0,0),0)
  canvas.create_oval(6,6,506,506,outline='black',width=1)

def drawellipse(c,canvas) :
  # translate center to 0,0
  # scale so distance from directrix to center is 500/2 = 250
  d = distance(*c.ad)  # distance between directrices
  scale = 500/d
  for i in range(2) :
    drawtpoint(canvas,c.foci[i],c.center,scale)
  for i in range(2) :
    drawtline(canvas,c.directrices[i],c.center,scale)
  # plot y = n sin t, x = m cos t, -pi->+pi rotated appropriately
  g = c.eccentricity
  dx,dy = tuple(map(float,c.directrix[:2]))
  k = 250*g
  m,n = k, k*sqrt(1-g*g)
  x0,y0 = m,0
  for t in range(1,257) :
    x,y = m*cos(tau*t/1024), n*sin(tau*t/1024)
    for r in (-1,1) :
      for s in (-1,1) :
        a,b = r*dx*x0+s*dy*y0, r*dy*x0-s*dx*y0
        c,d = r*dx*x+s*dy*y, r*dy*x-s*dx*y
        canvas.create_line(*tofloat(256+a,256-b,256+c,256-d))
    x0,y0 = x,y
    
def drawparabola(c,canvas) :
  # translate vertex to 0,0
  # scale so distance from focus to directrix is 512/2 = 256
  focus = c.focus
  vertex = c.vertex
  directrix = c.directrix
  d = distance(focus,directrix)    # signed!!!
  scale = 256/d
  drawtpoint(canvas,focus,c.vertex,scale)
  drawtline(canvas,directrix,vertex,scale)
  # plot y = x^2/4v [vertex = (0,v)] and rotated appropriately
  dx,dy = -directrix[1],directrix[0]
  x0,y0 = -362,362*362/512
  x0,y0 = dx*x0+dy*y0, dy*x0-dx*y0
  for x in range(-361,363) :
    y = x*x/512
    x,y = dx*x+dy*y, dy*x-dx*y
    canvas.create_line(*tofloat(256+x0,256-y0,256+x,256-y))
    x0,y0 = x,y

def drawhyperbola(c,canvas) :
  # translate center to 0,0
  # scale so distance from focus to center is 512/4 = 128
  foci = c.foci
  d = distance(*foci)
  scale = 250/d
  for i in range(2) :
    drawtpoint(canvas,foci[i],c.center,scale)
  for i in range(2) :
    drawtline(canvas,c.asymptotes[i],c.center,scale)
  for i in range(2) :
    drawtline(canvas,c.directrices[i],c.center,scale)
  # plot x = sinh t, y = cosht scaled and rotated
  g = c.eccentricity
  dx,dy = c.directrix[:2]
  k = 125/g
  m,n = k, k*sqrt(g*g-1)
  x0,y0 = m,0
  for t in range(1,257) :
    x,y = m*cosh(t/128), n*sinh(t/128)
    for r in (-1,1) :
      for s in (-1,1) :
        a,b = r*dx*x0+s*dy*y0, r*dy*x0-s*dx*y0
        c,d = r*dx*x+s*dy*y, r*dy*x-s*dx*y
        canvas.create_line(*tofloat(256+a,256-b,256+c,256-d))
    x0,y0 = x,y

drawdict = dict(
  empty = drawempty,
  point = drawpoint,
  line = drawline,
  doubled = drawline,
  parallel = drawplines,
  crossing = drawclines,
  plane = drawplane,
  circle = drawcircle,
  ellipse = drawellipse,
  parabola = drawparabola,
  hyperbola = drawhyperbola
)

def distance(a,b) :
  """Return distance between 2D points or lines a and b;
assume lines are in canonical form: sum of squares of x and y coeffs = 1"""
  if len(a) == 2 :
    if len(b) == 2 :
      return hypot(a[1]-b[1],a[0]-b[0])
    else :
      return a[0]*b[0]+a[1]*b[1]+b[2]
  else :
    if len(b) == 2 :
      return a[0]*b[0]+a[1]*b[1]+a[2]
    else :
      if a[0]*b[1]!=a[1]*b[0] :
        return 0
      else :
        return b[2]-a[2]

def easeyes() :
  """Make rationals easier to read"""
  xrational.__repr__ = xrational.__str__
  rational.__repr__ = rational.__str__ = lambda x:str(x.numerator) if x.denominator==1 else x.bstr()

from random import randint

def testconic() :
  """Return a "random" conic :
  choose six random integer coefficients from [-5,5] and use them to create a conic;
  check that conic is recreated from computed eccentricity, focus, and directrix"""
  coeffs = tuple(randint(-5,5) for _ in range(6))
  print(coeffs,end=' ',flush=True)
  C = conic(*coeffs)
  print(C.classification, C.coeffs)
  if C.classification == 'empty' :
    return C
  if C.classification == 'point' :
    return C
  if C.classification != 'circle' :
    try :
      for d in C.directrices :
        if not isclose(d[0]*d[0]+d[1]*d[1],1,abs_tol=1e-20) :
          print('directrix not normalized',d)
    except Exception :
      pass
  try :
    for a in C.axes :
      if not isclose(a[0]*a[0]+a[1]*a[1],1,abs_tol=1e-20) :
        print('axis not normalized',a)
  except Exception:
    pass
  try :
    for l in C.lines :
      if not isclose(l[0]*l[0]+l[1]*l[1],1,abs_tol=1e-20) :
        print('line not normalized',l)
  except Exception:
    pass
  try :
    l = C.line
    if not isclose(l[0]*l[0]+l[1]*l[1],1,abs_tol=1e-20) :
      print('line not normalized',l)
  except Exception:
    pass
  for j in range(len(C.foci)) :
    C2 = conic(eccentricity=C.eccentricity,
               focus=C.foci[j], directrix=C.directrices[j])
    for i in range(6) :
      if not isclose(C.coeffs[i],C2.coeffs[i],abs_tol=1e-20) :
        print(C.coeffs,'!=',C2.coeffs)
        break
  return C

def testconics(cnt) :
  """Run test cnt times; return set of classifications encountered"""
  d = set()
  for _ in range(cnt) :
    c = testconic()
    d.add(c.classification)
  return d

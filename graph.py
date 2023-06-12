"""undirected graph class"""

import sys
from collections import defaultdict
from itertools import permutations,product
from conversions import range, xrange, lmap, long
from matrix import matrix

class graph(object) :
  """Undirected graph
 Instance variables (read-only):
  n: the number of nodes, numbered 0 through n-1
  edges: a frozenset of edges, with each edge a pair (i,j) of nodes, 0<=i<j<n
  edgebits: an integer whose bits specify the edges,
    where edge (i,j) is at 1<<(i+j*(j-1)//2)
  degrees: a list indexed by node number, giving the degree of each node
  components: a list indexed by node number, giving the set of nodes comprising
    the connected component containing the node; connected nodes share their set
  laplacian: the laplacian matrix
 Methods:  __init__,__hash__,__repr__,__eq__,__ne__,
           __bool__, __nonzero__,__len__,__invert__,__and__,__or__,__xor__,
           complement,__iand__,__ior__,__ixor__
           remove, permute, isomorphism, degree, psdraw"""

  def __init__(self,n=0,edges=0) :
    """Create an undirected graph with numbered nodes given
  n, the number of nodes, and
  edges, a list, tuple, or {frozen}set of pairs (list, tuple, {frozen}set) of nodes, or
         an integer whose bits specify edges,
           where edge (i,j) is at 1<<(i+j*(j-1)//2), assuming i<j"""
    if not (isinstance(n,int) and n >= 0 and isinstance(edges,(list,tuple,set,frozenset,int,long))):
      raise ValueError("n must be non-negative int and edges must be list, tuple, set, frozenset, or int or long");
    self.__n = n;
    if isinstance(edges,(int,long)) :
      if not 0 <= edges < 1<<(n*(n-1)//2) :
        raise ValueError("edges out of range");
    else :
      es = set(map(lambda e : tuple(sorted(e)),edges));
      for e in es :
        if not (len(e) == 2 and isinstance(e[0],int) and isinstance(e[1],int) and
                0 <= e[0] < e[1] < n) :
          raise ValueError("Edge nodes must be in-range pairs of distinct nodes");
      edges = 0;
      for j in xrange(n-1,0,-1) :
        for i in xrange(j-1,-1,-1) :
          edges <<= 1;
          if (i,j) in es : edges += 1;
    self.__e = edges;

  def __hash__(self) :
    return hash((type(self),self.__n,self.__e));

  def __repr__(self) :
    return 'graph(%d,%s)'%(self.__n,str(tuple(sorted(self.edges))));

  def __bool__(self) :
    """Return True"""
    return True;

  __nonzero__ = __bool__

  def __len__(self) :
    """Return the number of edges"""
    return bin(self.__e).count('1');
    #the following is significantly slower, sadly
    #e = self.__e
    #c = 0;
    #while (e) :
    #  e &= e-1;
    #  c += 1;
    #return c;

  def degree(self,i=None) :
    """Return the degree of a specified node, or the average node degree"""
    n = self.__n;
    if i == None :
      return 2.0*len(self)/n if n else 0;
    if not 0 <= i < n : raise ValueError('Node not in graph')
    #c = 0;                                  # the old way
    #for e in self.edges : c += i in e;      # yaw dlo eht
    e = self.__e;
    c = bin((e >> (i*(i-1)//2)) & ((1<<i)-1)).count('1');
    for j in xrange(i+1,n) :
      c += 1 & (e >> (i+j*(j-1)//2));
    return c;

  @property
  def n(self) :
    """number of vertices"""
    return self.__n;

  @property
  def edgebits(self) :
    """bitmap of edges, edge (i,j) is at 1<<(i+j*(j-1)//2)"""
    return self.__e;

  @property
  def edges(self) :
    """frozenset of edges"""
    n = self.__n;
    e = self.__e;
    edges = [];
    for j in xrange(1,n) :
      for i in xrange(j) :
        if 1 & (e >> (i+j*(j-1)//2)) : edges.append((i,j));
    return frozenset(edges);

  @property
  def degrees(self) :
    """list of degrees of vertices"""
    n = self.__n;
    e = self.__e;
    a = [0 for i in xrange(n)];
    for j in xrange(1,n) :
      for i in xrange(j) :
        if 1 & (e >> (i+j*(j-1)//2)) :
          a[i] += 1;
          a[j] += 1;
    return a;

  @property
  def components(self) :
    """list of connected components of vertices"""
    n = self.__n;
    e = self.__e;
    d = lmap(lambda x:set([x]),xrange(n));
    for j in xrange(1,n) :
      for i in xrange(j) :
        if 1 & (e >> (i+j*(j-1)//2)) :
          if not d[i] is d[j] :
            a,b = i,j;
            if len(d[a]) < len(d[b]) : a,b = b,a;
            d[a] |= d[b];
            for v in d[b] : d[v] = d[a];
    return d;

  @property
  def laplacian(self) :
    """laplacian matrix"""
    n = self.__n;
    e = self.__e;
    m = matrix(n,n);
    for j in xrange(1,n) :
      for i in xrange(j) :
        if 1 & (e >> (i+j*(j-1)//2)) :
          m[i,j] = m[j,i] = -1;
          m[i,i] += 1;
          m[j,j] += 1;
    return m;

  def __ne__(self,other) :
    """Return False if self and other are the same graph, True otherwise"""
    return not (self == other);

  def __eq__(self,other) :
    """Return True if self and other are the same graph, False otherwise"""
    return isinstance(other,graph) and self.__n == other.__n and self.__e == other.__e;

  def isomorphism(self,other) :
    """Return an isomorphism from self to other, if any, else None"""
    if not isinstance(other,type(self)) : return None;
    n = self.__n;
    if other.__n != n : return None;
    if self.__e == other.__e : return range(n);
    c = len(self);
    if len(other) != c : return None;
    if c > n*(n-1)//4 :
      self = ~self;
      other = ~other;
    sd = self.degrees;
    od = other.degrees;
    if sorted(sd) != sorted(od) : return None;
    sc = self.components;
    oc = other.components;
    if sorted(map(len,sc)) != sorted(map(len,oc)) : return None;
    e = self.__e;
    f = other.__e;
    snd = [[] for i in xrange(n)];    # neighbor degrees
    ond = [[] for i in xrange(n)];
    for j in xrange(1,n) :
      for i in xrange(j) :
        if 1 & (e >> (i+j*(j-1)//2)) :
          snd[i].append(sd[j]);
          snd[j].append(sd[i]);
        if 1 & (f >> (i+j*(j-1)//2)) :
          ond[i].append(od[j]);
          ond[j].append(od[i]);
    # nodes with 0 or n-1 neighbors can each have their own equivalence class
    cp = cm = 0;    # init numbering for such s[elf] equivalence classes
    for x in snd :
      if not x :
        cp += 1;
        x[0:2] = 0,cp;
      elif len(x) == n-1 :
        del x[2:];
        cm -= 1;
        x[0:2] = 0,cm;
      else :
        x.sort();
    cp = cm = 0;    # init numbering for matching o[ther] equivalence classes
    for x in ond :
      if not x :
        cp += 1;
        x[0:2] = 0,cp;
      elif len(x) == n-1 :
        del x[2:];
        cm -= 1;
        x[0:2] = 0,cm;
      else :
        x.sort();
    if sorted(snd) != sorted(ond) : return None
    # create equivalence classes for nodes, then try permutations
    sdc = defaultdict(set);
    for i,d in enumerate(zip(map(tuple,snd),map(len,sc))) :
      sdc[d].add(i);
    odc = defaultdict(set);
    for i,d in enumerate(zip(map(tuple,ond),map(len,oc))) :
      odc[d].add(i);
    # keys are equivalence class instances, entries are node sets
    # possible criteria for node equivalence classes:
    #   degree, component size, sorted list of neighbor degrees
    # we're using component size + neighbor degrees (which is a refinement of degrees)
    # we could make better use of components: all elements within a component
    #   must move together to an equivalent component [this only matters when
    #   two components have the same size]
    # try matching nodes in corresponding equivalence classes
    # if get equality, the permutation
    # but when all such matchings are exhausted, return None
    g = graph(n);
    for p in _pp(n,[tuple(sdc[i]) for i in sdc], [tuple(odc[i]) for i in sdc]) :
      g.__e = e;
      g.permute(p);
      if g.__e == f : return p;
    return None;

  def permute(self,p) :  # p is list with the new node numbers
    """Renumber the nodes of the graph;
  the permutation p is specified as a map (list, tuple, dict)
  from node number to new node number"""
    n = self.__n;
    if sorted(p) != range(n) : raise ValueError('Not a permutation');
    #return graph(n, map(lambda e: map(lambda v: p[v], e), self.edges));
    e = self.__e;
    c = 0;
    for j in xrange(1,n) :
      for i in xrange(0,j) :
        a,b = (p[i],p[j]) if p[i] < p[j] else (p[j],p[i]);
        c |= (1 & (e >> (i+j*(j-1)//2))) << (a+b*(b-1)//2);
    self.__e = c;

  def psdraw(self) :    # draw graph
    """Return PostScript code to draw graph centered at (0,0) with nodes on unit circle"""
    return """/c {/n exch def [ 0 1 n 1 sub {360 mul n div dup sin exch cos [0 0] astore} for ] /nodes exch def} bind def
/d {nodes exch get aload pop moveto closepath stroke} bind def
/e {nodes exch get aload pop moveto nodes exch get aload pop lineto stroke} bind def
/a {gsave currentlinewidth 2 mul setlinewidth 0 1 n 1 sub /d load for grestore} bind def
%d c a %s
"""%(
      self.__n,' '.join(['%d %d e'%(min(e),max(e)) for e in self.edges]));

  def __ior__(self,other) :
    """Return graph with union of all the edges, n is max of the two graphs"""
    if not isinstance(other,graph) : raise TypeError;
    self.__n = max(self.__n,other.__n);
    self.__e |= other.__e;
    return self;

  def __iand__(self,other) :
    """Return graph with intersection of all the edges, n in min of the two graphs"""
    if not isinstance(other,graph) : raise TypeError;    
    self.__e &= other.__e;
    self.__n = min(self.__n,other.__n);
    return self;
   
  def __ixor__(self,other) :
    """Return graph with xor of all the edges, n is max of the two graphs"""
    if not isinstance(other,graph) : raise TypeError;
    self.__n = max(self.__n,other.__n);
    self.__e ^= other.__e;
    return self;

  def __or__(self,other) :
    """Return graph with union of all the edges, n is max of the two graphs"""
    if not isinstance(other,graph) : raise TypeError;
    return graph(max(self.__n,other.__n), self.__e | other.__e);

  def __and__(self,other) :
    """Return graph with intersection of all the edges, n in min of the two graphs"""
    if not isinstance(other,graph) : raise TypeError;    
    return graph(min(self.__n,other.__n), self.__e & other.__e);
   
  def __xor__(self,other) :
    """Return graph with xor of all the edges, n is max of the two graphs"""
    if not isinstance(other,graph) : raise TypeError;
    return graph(max(self.__n,other.__n), self.__e ^ other.__e);

  def complement(self) :
    """Complement the graph's set of edges"""
    n = self.__n;
    self.__e ^= (1<<(n*(n-1)//2))-1;

  def __invert__(self) :
    """Return graph with complement of edges"""
    n = self.__n;
    return graph(n, (1<<(n*(n-1)//2))-1-self.__e);

  def remove(self,*items) :
    """Remove the specified nodes and edges; then renumber remaining nodes;
nodes are specified by number, edges by pairs of original node numbers;
remaining nodes are renumbered consecutively from 0, but not reordered"""
    if not items : return self;
    nodes = [x for x in items if isinstance(x,(int,long))];
    edges = [x for x in items if isinstance(x,(list,tuple,set,frozenset))];
    if len(nodes)+len(edges) < len(items) :
      raise TypeError("only nodes and edges can be removed");
    n = self.__n;
    if nodes :
      nodes.sort();
      if nodes[0] < 0 or nodes[-1] >= n :
        raise ValueError("nodes out of range");
    es = set(map(lambda e : tuple(sorted(e)),edges));
    for e in es :
      if not (len(e) == 2 and isinstance(e[0],int) and isinstance(e[1],int) and
              0 <= e[0] < e[1] < n) :
        raise ValueError("Edge nodes must be in-range pairs of distinct nodes");
    # first, remove edges
    for (i,j) in es :
      self.__e &= ~(1<<(i+j*(j-1)//2));
    # now, remove nodes
    if nodes :
      p = range(n);
      nodes.append(n);
      for i,j in enumerate(nodes[:-1],1) :
        p[j] = n-i;
        for k in range(j+1,nodes[i]) :
          p[k] -= i;
      n -= i;
      self.permute(p);
      self.__e &= (1<<(n*(n-1)//2))-1;
      self.__n = n;

def _pp(n,po,p) :
  # po and p are corresponding lists of nodelists,
  #  each list comprising nodes 0 thru n-1
  # each nodelist is an equivalence class of nodes
  #  corresponding nodelists have the same length
  # po contains source nodes, p contains destination nodes
  # we generate permutations taking source nodes to destination nodes,
  #  where (source node, destination node) come from corresponding nodelists
  q = [0]*n;
  for x in product(*map(permutations,p)) :
    for i,pi in enumerate(po) :    # get ith source nodelist
      for j,pij in enumerate(pi) : # get jth node in ith source nodelist
        q[pij] = x[i][j];    # map to jth node in permuted ith source nodelist
    yield q;

def permuted(g,p=None) :  # g is a graph, p is list with the new node numbers
  """Return a graph isomorphic to g but with node numbers permuted;
the permutation p is specified as a map (list, tuple, dict)
from node number to new node number"""
  g = graph(g.n,g.edgebits);
  if p != None : g.permute(p);
  return g;

def removed(g,*items) :
  """Return a copy of g with the specified nodes and edges removed;
nodes are specified by number, edges by pairs of node numbers;
remaining nodes are renumbered consecutively from 0, but not reordered"""
  g = graph(g.n,g.edgebits);
  g.remove(*items);
  return g;

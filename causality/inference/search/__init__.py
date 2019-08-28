import networkx as nx
import itertools

"""
This is an implementation of the IC* (Inductive Causation with latent
variables) algorithm as described in _Causality_ by Judea Pearl, 2000.
"""

try:
    xrange
except NameError:
    xrange = range

class SearchException(Exception):
    pass

class IC():
    def __init__(self, independence_test, alpha=0.05, k=None):
        self.independence_test = independence_test
        self.alpha = alpha
        self.separating_sets = None
        self._g = None
        self.max_k = k

    def search(self, data, variable_types):
        self._build_g(variable_types)
        self._find_skeleton(data, variable_types)
        self._orient_colliders()

        added_arrows = True
        # add arrows recursively
        while added_arrows:
            R1_added_arrows = self._apply_recursion_rule_1()
            R2_added_arrows = self._apply_recursion_rule_2()
            """
             理论上会出现双箭头+marked的情况，由rule1得到单箭头mark，由rule2得到另一个方向的箭头，这符合paper的算法，但不符合实际，
             能满足rule1则不可能满足rule2因为显然已经不是一个collider的结构也就是a与b不独立，那么既然a与b没有相邻，则a与b一定given c
             条件独立。则只有3种情况，a->c->b,a<-c<-b,a<-c->b,因为a->c了，所以只有可能c->b，所以这个时候不应该在通过rule2加箭头
            """
            added_arrows = R1_added_arrows or R2_added_arrows

        return self._g

    def _build_g(self, variable_types):
        """
        This initializes a complete graph over the variables.  We'll run
        independence tests on the complete graph to cut edges by trying to
        find separating sets.
        """
        self._g = nx.Graph()
        self._g.add_nodes_from(variable_types.keys())
        for var, var_type in variable_types.items():
            self._g.node[var]['type'] = var_type
        edges_to_add = []
        # 做全连通图
        for (node_a, node_b) in itertools.combinations(self._g.node.keys(), 2):
            edges_to_add.append((node_a,node_b))
        self._g.add_edges_from(edges_to_add, marked=False)

    def _apply_recursion_rule_1(self):
        added_arrows = False
        for c in self._g.nodes():
            for (a,b) in itertools.combinations(self._g.neighbors(c), 2):
                if not self._g.has_edge(a,b):
                    if c in self._g[a][c]['arrows'] and c not in self._g[b][c]['arrows'] and not (b in self._g[b][c]['arrows'] and self._g[b][c]['marked']):
                        # 根据step2，上面条件满足证明c在S_ab之中，否则会有一个b到c的箭头，所有c肯定d-seperate，所以c肯定指向b
                        if b not in self._g[b][c]['arrows']:
                            self._g[b][c]['arrows'].append(b)
                        self._g[b][c]['marked'] = True
                        added_arrows = True
                    if c in self._g[b][c]['arrows'] and c not in self._g[a][c]['arrows'] and not (a in self._g[a][c]['arrows'] and self._g[a][c]['marked']):
                        if a not in self._g[a][c]['arrows']:
                            self._g[a][c]['arrows'].append(a)
                        self._g[a][c]['marked'] = True
                        added_arrows = True
        return added_arrows

    def _apply_recursion_rule_2(self):
        added_arrows = False
        for (a,b) in self._g.edges():
            if b not in self._g[a][b]['arrows']:
                if self._marked_directed_path(a,b):
                    if b not in self._g[a][b]['arrows']:
                        if not _g[a][b]['marked']:
                            self._g[a][b]['arrows'].append(b)
                    added_arrows = True
        return added_arrows

    def _marked_directed_path(self,a,b):
        seen = [a]
        neighbors = [(a,neighbor) for neighbor in self._g.neighbors(a)]
        while neighbors:
            (parent, child) = neighbors.pop()
            if child in self._g[parent][child]['arrows'] and self._g[parent][child]['marked']:
                if child == b:
                    return True
                if child not in seen:
                    neighbors += [(child, neighbor) for neighbor in self._g.neighbors(child)]
                seen.append(child)
        return False


    def _orient_colliders(self):
        for v_i, v_j in self._g.edges():
            # _g[v_i]是v_i全部的neighbor
            self._g[v_i][v_j]['arrows'] = []
        # 2 step
        for v_c in self._g.nodes():
            for (v_a,v_b) in itertools.combinations(self._g.neighbors(v_c), 2):
                if not self._g.has_edge(v_a,v_b):# for each pair of nonadjacent variables v_a and v_b with common neighbor v_c
                    # c与ab有关，且a和b given c条件独立，所以a,c,b形成一个collider
                    if v_c not in self.separating_set(v_a,v_b):
                        if v_c not in self._g[v_a][v_c]['arrows']:
                            self._g[v_a][v_c]['arrows'].append(v_c)
                        if v_c not in self._g[v_b][v_c]['arrows']:
                            self._g[v_b][v_c]['arrows'].append(v_c)

    def separating_set(self, xi, xj, data=None, variable_types=None):
        if not self.separating_sets and data and variable_types:
            if not self._g:
                self._build_g(variable_types)
            self._find_skeleton(data, variable_types)
        elif not self.separating_sets and not (data and variable_types):
            raise SearchException("Can't measure separating sets: Need data and var types.")
        if (xi,xj) in self.separating_sets:
            return self.separating_sets[(xi,xj)]
        elif (xj,xi) in self.separating_sets:
            return self.separating_sets[(xj,xi)]
        else:
            return False

    def _find_skeleton(self, data, variable_types):
        """
        For each pair of nodes, run a conditional independence test over
        larger and larger conditioning sets to try to find a set that
        d-separates the pair.  If such a set exists, cut the edge between
        the nodes.  If not, keep the edge.
        """
        self.separating_sets = {}
        if not self.max_k:
            self.max_k = len(self._g.node)+1
        for N in range(self.max_k + 1):
            for (x, y) in list(self._g.edges()):
                x_neighbors = list(self._g.neighbors(x))
                y_neighbors = list(self._g.neighbors(y))
                z_candidates = list(set(x_neighbors + y_neighbors) - set([x,y]))
                # 对于一个edge上的两个node x和y，如果能找到集合z，s.t. x和y given z条件独立，则x和y的线取掉
                for z in itertools.combinations(z_candidates, N):
                    test = self.independence_test([y], [x], list(z),
                        data, self.alpha)
                    if test.independent():
                        self._g.remove_edge(x,y)
                        self.separating_sets[(x,y)] = z
                        break

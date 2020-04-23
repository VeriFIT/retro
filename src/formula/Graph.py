
from copy import *

class Graph:

    def __init__(self, verts, edges, labels=None):
        self.verts = verts
        self.edges = edges
        self.labels = labels


    @staticmethod
    def _graph_in_edges(edges, verts):
        cnt_dict = dict()
        for v in verts:
            cnt_dict[v] = 0
        for _, to in edges:
            cnt_dict[to] += 1
        return cnt_dict


    @staticmethod
    def _delete_vertice(edges, v):
        ret = list()
        for fr, to in edges:
            if fr == v or to == v:
                continue
            ret.append((fr, to))
        return ret


    def sort_dep_graph(self):
        ret = list()
        edges = copy(self.edges)
        verts = copy(self.verts)
        while len(verts) > 0:
            in_dict = Graph._graph_in_edges(edges, verts)
            min_vec = min(in_dict, key=in_dict.get)
            verts.remove(min_vec)
            ret.append(min_vec)
            edges = Graph._delete_vertice(edges, min_vec)
        return ret

#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Mon Feb  7 20:50:49 2022

@author: xiaoxu
"""

def offset(node_addrs, ofst):
    if isinstance(node_addrs, int):
        return node_addrs + ofst
    return tuple([offset(addr, ofst) for addr in node_addrs])

def flatten(nodes):
    flat = []
    for addr in nodes[1:]:
        if isinstance(addr, int):
            flat.append(addr)
        else:
            flat += flatten(addr)
    return flat

def add(nodes1, nodes2):
    '''
    nodes1 and nodes2 are assumed to contain unique elements
    '''
    if len(nodes1) == 0: return nodes2
    if len(nodes2) == 0: return nodes1 
    
    nodes1 = list(nodes1)
    nodes2 = list(nodes2)
    
    for item2 in nodes2[1:]:
        if isinstance(item2, int) and not item2 in nodes1:
            nodes1.append(item2)
        else:
            present = False
            for item1 in nodes1:
                if not isinstance(item1, int) and item1[0] == item2[0]:
                    new_item = add(item1, item2)
                    nodes1.remove(item1)
                    nodes1.append(new_item)
                    present = True
                    break
            if not present:
                nodes1.append(item2)
                
    return nodes1

def substract(nodes1, nodes2):
    if len(nodes2) < 2 : 
        return nodes1 if len(nodes1) > 1 else []
    
    nodes1 = list(nodes1)
    nodes2 = list(nodes2)
    
    for item2 in nodes2[1:]:
        if isinstance(item2, int):
            if item2 in nodes1:
                nodes1.remove(item2)
        else:
            for item1 in nodes1:
                if not isinstance(item1, int) and item1[0] == item2[0]:
                    new_item = substract(item1, item2)
                    nodes1.remove(item1)
                    if new_item != []:
                        nodes1.append(new_item)
                    break
    if len(nodes1) == 1:
        return []
    return nodes1


def nodes_remove_links(unlinked_nodes, links_config):
    '''
    remove linked nodes from unlinked_nodes given a links_config (K config)
    '''
    if len(unlinked_nodes) == 0: return ()
    if unlinked_nodes == [1]: return ()
    linked_nodes = [links[1] for links in links_config]
    result =  _nodes_remove_links(unlinked_nodes, linked_nodes)
    if len(result) == 1:
        return ()
    return result

def _nodes_remove_links(unlinked_nodes, linked_nodes):
    if isinstance(unlinked_nodes, int):
        if unlinked_nodes in linked_nodes: return ()
        return unlinked_nodes

    if len(unlinked_nodes) == 0: return ()

    l = []
    for item in unlinked_nodes[1:]:
        i = _nodes_remove_links(item, linked_nodes)
        if i != ():
            l.append(i)
    if len(l) == 0:
        return ()
    return tuple([unlinked_nodes[0]]+l)    



def seperate(nodes):
    '''
    return a list of nodes and each entry is a single nodes.
    e.g. for nodes (0,1,(1,4,5))
    return [(0,1), (0,(1,4)), (0,(1,5))]
    '''
    #base case, nodes only contain one nodes, e.g. (1,5)
    if len(flatten(nodes)) == 1:
        return [nodes]
    
    nodes_sep = []
    for node in nodes[1:]:
        if isinstance(node, int):
            nodes_sep.append((nodes[0], node))
        else:
            for c_node in seperate(node):
                nodes_sep.append((nodes[0], c_node))
    return nodes_sep


def parent(node):
    '''
    return the parent of a node.
    e.g. for (0,(1,(4,9))) return (0,(1,4)).

    '''
    if node[1] == node[0]:
        raise Exception("don't know the parent's info of node "+str(node))
    if isinstance(node[1], int):
        return (node[0], node[0])
    
    cnode = parent(node[1])
    if cnode[1] == cnode[0]:
        return (node[0], cnode[0])
    return (node[0], cnode)


def ancestors(node):
    '''
    return the list of parent node of a node. 
    e.g. 
    
    (0,(1,(4,9))) return [(0,0), (0,1), (0,(1,4))].
    
    note that for (0,0) should return []
    '''
    parent_ = parent(node)
    
    if parent_[0]==parent_[1]: return [parent_]
    
    return ancestors(parent_)+ [parent_]
    
    
def is_ancestor(nodeA, nodeB):
    '''
    check if nodeA is ancestor of nodeB
    e.g. (0,1) is ancestor of (0,(1,(4, 5)))
    '''
    return nodeA in ancestors(nodeB)


def enclose(pair, node):
    '''
    By enclosing, it means
    node has nodeA as ancestor but is not the ancestor of B.
    '''
    return is_ancestor(pair[0], node) and not is_ancestor(pair[1],node)


def add_parent(node, pnode):
    if node[0] != node[1]: return (pnode, node)
    return (pnode, node[0])
    

def pair_add_parent(pair, pnode):
    return (add_parent(pair[0],pnode), add_parent(pair[1],pnode))

def pairs_add_parent(pairs, pnode):
    return tuple([pair_add_parent(pair, pnode) for pair in pairs])

def to_tuple(nodes):
    if isinstance(nodes, int): return nodes
    return tuple([to_tuple(node) for node in nodes])
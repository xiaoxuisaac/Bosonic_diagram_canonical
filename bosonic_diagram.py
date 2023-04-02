#!/usr/bin/env python3
# -*- coding: utf-8 -*-
from copy import deepcopy
from collections import Counter
import itertools
from more_itertools import distinct_permutations
from sympy import Symbol, Rational, Mul
from sympy import prod, factorial
from sympy import flatten
from sympy import integrate
from scipy.special import comb
import numpy as np
import math

import warnings
import node_algebra as nd_al

#TODO: multi-mode, multi-tone case; save as an attribute and decide
# the structure so it knows mode and tone



def slice_list_n(lst, ns, identical = False):
    '''
    ns = [n1, n2, ...], each n_i gives the capacity of each bin
    return all configurations of dributing balls in lst to the bins 
    '''
    
    if len(ns) == 1:
        return [(tuple(sorted(lst)),)]
    
    first_configs = []
    
    for l in itertools.combinations(lst, ns[0]):
        first_configs.append(tuple(sorted(l)))
    
    first_configs = list(set(first_configs))
    
    configs = []
    for first_config in first_configs:
        right_lst = list(deepcopy(lst))
        for item in first_config:
            right_lst.remove(item)
        right_configs = slice_list_n(right_lst, ns[1:])
        config_nested = list(itertools.product([first_config], right_configs))
        config = []
        for c in config_nested:
            config.append(tuple([c[0]]+list(c[1])))
        configs += config
        
    if identical:
        sorted_configs = []
        for c in configs:
            sorted_configs.append(tuple(sorted(c)))
        return sorted(list(set(sorted_configs)))
    return sorted(configs)

def combine(lst1, lst2):
    '''combine lst1 and lst2 while maintain the order of element within each list.
    '''
    lst_configs = []
    n = len(lst1)+len(lst2)
    for lst1_indices in itertools.combinations(range(n), len(lst1)):
        l1_counter = 0
        l2_counter = 0
        lst = []
        for i in range(n):
            if i in lst1_indices:
                lst.append(lst1[l1_counter])
                l1_counter+=1
            else:
                lst.append(lst2[l2_counter])
                l2_counter+=1
        lst_configs.append(lst)
    return lst_configs

def all_combinations(lst):
    """Returns a list of all possible combinations of items in lst."""
    # create a list of tuples where each tuple represents an item and its absence
    options = [(item, None) for item in lst]
    # use itertools.product to generate all possible combinations of options
    combinations = itertools.product(*options)
    # convert each combination tuple to a list and remove the None values
    result = [list(filter(lambda x: x is not None, c)) for c in combinations]
    return result

def index_mapping(lst1, lst2):
   """Returns a list where the i-th element is the index of lst2[i] in lst1."""
   result = []
   for item in lst2:
        index = lst1.index(item)
        result.append(index)
        # remove the found item from lst1 to find the next occurrence
        lst1 = lst1[:index] + [None]+lst1[index+1:]
   return result

def star_factor_ops(factors_ops_dict1, factors_ops_dict2, offset = 0):
    
    factors_ops_dict = {}
    for i, (hbar1, factor_ops1) in enumerate(factors_ops_dict1.items()):
        for j, (hbar2, factor_ops2) in enumerate(factors_ops_dict2.items()):
            factor12 = factor_ops1[0]*factor_ops2[0]
            for star_hbar in range(min(factor_ops1[1][0][0],factor_ops2[1][0][1])+1):
                ops, factor = _star_prod(factor_ops1[1] ,factor_ops2[1],
                                         star_hbar)
                
                for ofi  in range(1, 1+offset):
                    factor = Rational(factor,ofi+star_hbar)
                
                factor *= factor12
                hbar = hbar1 + hbar2 + star_hbar
                
                old_factor_ops = factors_ops_dict.get(hbar, (0,ops))
                old_factor_ops = (old_factor_ops[0]+factor, old_factor_ops[1])
                factors_ops_dict[hbar] = old_factor_ops 
                
    return factors_ops_dict

star_prod_dict = {}
def _star_prod(l_power, r_power, star_order):
    # TODO: multimode
    key = (l_power[0][0], r_power[0][1], star_order)
    
    if star_order == 0:
        count = 1
    else:
        count = star_prod_dict.get(key, None)
        if count == None:
            count = comb(key[0], star_order)*comb(key[1], star_order)\
                    * math.factorial(star_order)

                    
            star_prod_dict[key] = count
    power = [[l_power[0][0]+r_power[0][0]-star_order, 
              l_power[0][1]+r_power[0][1]-star_order]]
    
    return power, int(count)



class Tree():
    counter = 0 # unique id
    all_trees = []

    
    #leaves_dict is only populated by have_leaves. once it is populated
    # for a certain key, the list should be complete
    # Tree instance should only be created from have_leaves.
    leaves_delta_dict = {}
    @classmethod
    def have_leaves(cls, n, even_case = False, deltas = 0):
        addrs = cls._have_leaves(n,even_case, deltas )
        return cls.at(addrs)

    def __init__(self, children_addrs, leaves_count = 0, delta_count = 0):
        #TODO: explicitly ensure the constructor is private
        self.addr = self.__class__.counter
        self.__class__.counter += 1
        self.__class__.all_trees.append(self)
        self.children_addrs = sorted(children_addrs)
        self.leaves_count = leaves_count
        self.delta_count = 0



    #leaves_delta_dict is only populated by _have_leaves_even_case. once it is populated
    # for a certain key, the list should be complete
    @classmethod
    def _have_leaves(cls, n, even_case = False, deltas = 0):
        ''' return the list of address of tree each containing n total leaves
        '''
        if (n,deltas) in cls.leaves_delta_dict.keys():
            return cls.leaves_delta_dict[(n,deltas)]

        if n == 1 and deltas == 0: # base case, when a tree has no child
            tree = Tree([], n, deltas)
            cls.leaves_delta_dict[(n,0)] = [tree.addr]
            return cls.leaves_delta_dict[(n,0)]
        
        if even_case and n%2 == 0:
            raise Exception("even-way mixer only take odd number of inputs")
        
        cls.leaves_delta_dict[(n,deltas)] = []
        
        if deltas != 0:
            trees_delta = cls._have_leaves(n, even_case, deltas - 1)
            trees = []
            for tree in trees_delta:
                trees.append(Tree([tree], n).addr)
            cls.leaves_delta_dict[(n,deltas)] += trees
            
        for k in range(2, n+1)[::-1]:
            if not even_case or k%2 == 1:
                chilren_leaves_configs = cls.partitions_com(n, k, 1, even_case)
                children_delta_configs = cls.partitions(deltas, k)
                children_addrs_configs_all = []
                trees_addrs = []
                for chilren_leaves in chilren_leaves_configs:
                    for children_delta in children_delta_configs:
                        children_addrs_configs = []
                        for i, child_leaf in enumerate(chilren_leaves):
                            child_addrs = cls._have_leaves(child_leaf, even_case, children_delta[i])
                            children_addrs_configs.append(child_addrs)
                        children_addrs_configs_ts = itertools.product(*children_addrs_configs)
                        children_addrs_configs_all += list(children_addrs_configs_ts)
                
                for children_addrs in children_addrs_configs_all:
                    if cls.find_by_children(children_addrs, trees_addrs) is None:
                        tree = Tree(children_addrs, n, deltas) 
                        trees_addrs.append(tree.addr) 
                cls.leaves_delta_dict[(n,deltas)] += trees_addrs
                
            
        return cls.leaves_delta_dict[(n,deltas)]


    @classmethod
    def partitions_com(cls, n, k, l=1, even_case = False):
        '''n is the integer to partition, k is the length of partitions, 
        l is the min partition element size'''
        if k < 1:
            return []
        if k == 1:
            if n >= l:
                if even_case and n%2 == 0:
                    raise Exception("even-way mixer only take odd number of inputs")
                return [[n]]
        r = []
        for i in range(l,n+1):
            if not even_case or i%2 == 1:
                for result in cls.partitions_com(n-i,k-1,i, even_case):
                    r.append([i]+result)
        return r
    
    partitions_map = {}
    @classmethod
    def partitions(cls, n, k):
        '''
        return the list of configurations to put n hbar's in k slots
        https://stackoverflow.com/questions/28965734/general-bars-and-stars        
        '''
        result = cls.partitions_map.get((n,k), [])
        if result != []:
            return cls.partitions_map[(n,k)]
        for c in itertools.combinations(range(n+k-1), k-1):
            result.append([b-a-1 for a, b in zip((-1,)+c, c+(n+k-1,))])
        
        cls.partitions_map[(n,k)] = result
        return result


    @classmethod
    def find_by_children(cls, addrs, scope = None, leaves_count = 0):
        if addrs == []:
            return None

        if scope == None:
            if leaves_count == 0:
                delta_count = 0
                for addr in addrs:
                    leaves_count += cls.at(addr).leaves_count
                    delta_count += cls.at(addr).delta_count
            if (leaves_count,delta_count) not in cls.leaves_delta_dict: return None
            scope = cls.leaves_delta_dict[(leaves_count,delta_count)]

        for tree_addr in scope:
            if Counter(addrs) == Counter(cls.at(tree_addr).children_addrs):
                # goes through each element of trees_addrs, finds their address
                # and then obtains the children's address and checks with addrs
                return cls.at(tree_addr)
        return None


    @classmethod
    def count_leaves(cls, addrs):
        count = 0
        for addr in addrs:
            count += Tree.at(addr).leaves_count
        return count


    @classmethod
    def at(cls, addrs):
        if type(addrs) is int:
            return cls.all_trees[addrs]
        return [cls.at(addr) for addr in addrs]

    def __str__(self, offset = 0):
        if self.children_addrs == []:
            return str(offset)+'lf'
        
        s = str(offset)
        offset+=1
        
        c = ''
        for tree in self.at(self.children_addrs):
            c += tree.__str__(offset) + ','
            offset += tree.node_number
        c = c[:-1]
        
        
        if len(self.children_addrs) == 1:
            s += 'd-'+c
        else:
            s += '['+c+']'
        return s

    def __repr__(self):
        return self.__str__()+"@"+str(self.addr)


    #### node removing
    
    @property
    def node_number(self):
        '''
        return the number of node including the root one

        '''
        if '_node_number' in self.__dict__.keys():
            return self._node_number
        counter = 1
        for child_addr in self.children_addrs:
            counter += self.at(child_addr).node_number
        self._node_number = counter
        return self._node_number
    
    def remove(self, node):
        if '_remove_node_dict' not in self.__dict__.keys():
            self._remove_node_dict = {}
            
        if node in self._remove_node_dict:
            return self._remove_node_dict[node]
        
        counter = 1
        children_addrs = []
        for child_addr in self.children_addrs:
            if node == counter:
                children_addrs += [0]
            elif node > counter and node < counter + Tree.at(child_addr).node_number:
                children_addrs += [self.at(child_addr).remove(node-counter).addr]
            else:
                children_addrs += [child_addr]
            counter += Tree.at(child_addr).node_number
                
        return self.find_by_children(children_addrs)


class Network():
        
    is_even = False
    counter = 1
    all_networks = {}  # taddr is key of the dict. 
                        #each entry is a list of Network instance


    @classmethod
    def create(cls, taddr, children_addrs, sources_addrs = [], freq = 0):
        ''' Create an instance if it doesnt exist
        TODO: This is not needed.
        '''
        # if taddr in cls.all_networks.keys():
            # for network in cls.all_networks[taddr]:
                # if Counter(children_addrs) == Counter(network.children_addrs):
                    # return network

        return cls(taddr, children_addrs, sources_addrs, freq)



    # only _from_tree_sources_unidir* can call __init__ and create
    def __init__(self, taddr, children_addrs, sources_addrs = [], freq =  0):#, even_only = False):
        ''' This function only creates instance of annihilator type. Its conjugate is implied
        by a "virtual address" as the negative of the annihilator type
        '''
        self.taddr = taddr

        # if the tree is not already present
        if taddr not in self.all_networks.keys():
            self.all_networks[taddr] = []
            Network(taddr, [], sources_addrs = [Symbol('vacant')], freq = 0)

        self.naddr = len(self.all_networks[taddr])
        self.children_addrs = children_addrs
        self._nodes_dict_ = {}
        if children_addrs == []:
            self.is_source =  True
            self._freq = freq
            self._propag = 1
            self._counting_factor = 1
            self._composite_mixing_strength = 1
            self._sources_addrs = [self.addr]
            self._node_number = 1
            # if the network is a leaf, returning 1
        else:
            if sources_addrs != []:
                self._sources_addrs = sources_addrs
            self.is_source =  False

        self.all_networks[taddr].append(self)


    

    @classmethod
    def set_X0(cls, X = [((Symbol('A'), Symbol('omega_{o}'), Symbol('\sqrt{\lambda_1}')),
                          (Symbol('B'), Symbol('omega_{oB}'),Symbol('\sqrt{\lambda_2}'))),
                         ((Symbol('xi_1'), Symbol('omega_{d1}')), 
                          (Symbol('xi_2'), Symbol('omega_{d2}')))]): 
        #first tuple (source_name, second source_freq)
        
        if type(X[0][0]) == Symbol:
            X[0] = (X[0],)
        if type(X[1][0]) == Symbol or type(X[1][0]) != tuple:
            X[1] = (X[1],)
        
        #dictionary of sources, key is the addr, (whether is mode, name, freq)
        cls.X0 = {}
        cls.modes = []
        taddr = Tree.have_leaves(1)[0].addr

        for i , x in enumerate(X[0]):
            s = cls(taddr, [], freq = x[1])
            cls.X0[s.addr] = (True, x[0], x[1], i)
            cls.X0[cls.conj_addr(s.addr)] = (True, x[0].conjugate(), x[1], i)
            cls.modes.append((x[0], x[0].conjugate()))
            if not isinstance(x[1], (Symbol, Rational, int, Mul)):
                warnings.warn('frequency being a Float number may cause problem.\
                              Rational type is suggested.')
            
        cls.modes_number = i+1
        for i , x in enumerate(X[1]):
            s = cls(taddr, [], freq = x[1])
            cls.X0[s.addr] = (False, x[0], x[1])
            cls.X0[cls.conj_addr(s.addr)] = (False, x[0].conjugate(), x[1], i)
            if not isinstance(x[1], (Symbol, Rational, int, Mul)):
                warnings.warn('frequency being a Float number may cause problem.\
                              Rational type is suggested.')
        return

    commutator = Symbol("hbar", real = True)
    @classmethod 
    def set_commutator(cls, hbar):
        cls.commutator = hbar

    mixers = {}
    @classmethod
    def set_mixer(cls, mixing_strengths):
        cls.mixers = mixing_strengths
    #### properties

    @property
    def addr(self):
        return (self.taddr, self.naddr)


    @property
    def sources_addrs(self):
        '''
        given a network, finds the sources as a list of source indices
        '''
        if '_sources_addrs' in self.__dict__.keys():
            return self._sources_addrs
        else:
            _sources_addrs = []
            for addr in self.__dict__['children_addrs']:
                positive_addr = self.positive_addr(addr)
                c_sources_addrs = self.at(positive_addr).sources_addrs
                
                if positive_addr != addr:
                    c_sources_addrs = self.conj_addr(c_sources_addrs)
                
                _sources_addrs += c_sources_addrs
                
        self._sources_addrs = _sources_addrs
        return self._sources_addrs


    near_resonant = []
    @classmethod
    def set_near_resonant(cls, freq):
        if type(freq) is list:
            cls.near_resonant += freq
        else:
            cls.near_resonant.append(freq)

    @property
    def freq(self):
        if '_freq' in self.__dict__.keys():
            return self._freq
        freq = 0
        # if sources were pre-determined, find the frequency from them rather than recursively.
        if False and '_sources_addrs' in self.__dict__:
            for source_addr in self._sources_addrs:
                positive_addr = self.positive_addr(source_addr)
                
                if source_addr == positive_addr:
                    freq += self.at(positive_addr).freq
                else:
                    freq += (-1)* self.at(positive_addr).freq
        else:
            for addr in self.children_addrs:
                if addr != self.positive_addr(addr):
                    # when the address tuple is negative
                    freq += (-1)*self.at(self.conj_addr(addr)).freq
                else:
                    freq += self.at(addr).freq
        self._freq  = freq
        return self._freq


    @property
    def is_resonant(self):
        #TODO multimode
        if self.freq == self.at((0, 1)).freq: return True
        return self.freq in self.near_resonant


    #### (construct from sources)

    # key is (t_addr, list of sources_addrs) value is the list of addr of networks
    # only addr > 0 is stored.
    #this dict should only be updated inside _from_tree_sources_*.
    # i.e. once an entry is created, it needs to be complete
    naddrs_dict_tree_sources = {}

    @classmethod
    def with_sources(cls, sources_names, even_case = False, deltas = 0, tree_index = -1):
        '''
        returns all the networks given the sources
        '''
        #TODO: make the even case more elegent
        cls.is_even = even_case
        
        # sources_addrs = 0
        # sources_addrs = []
        # for name in sources_names:
        #     sources_addrs.append(cls._source_names2addrs(name))
        
        sources_addrs = cls._source_names2addrs(sources_names)
        
        networks_addrs = []
        for i, tree in enumerate(Tree.have_leaves(len(sources_names), even_case, deltas)):
            if tree_index >= 0 and i != tree_index:
                continue
            networks_addrs += cls._from_tree_sources_unidir(tree, sources_addrs, even_case)
        return cls.at(networks_addrs)


    @classmethod
    def _from_tree_sources_unidir(cls, tree, sources_addrs, even_case = False):
        ''' return addrs of all networks have underlying graph of the “tree” with
        external inputs whose addresses are sources_addrs. Only the address of
        the networks with output traveling AWAY from the mixer is returned.
        Parameter:
            inputs_addrs: list of input addresses associated with each source/leaf network
        '''
                
        sources_addrs_c = cls.conj_addr(sources_addrs)
        sources_addrs = tuple(sorted(sources_addrs))
        sources_addrs_c = tuple(sorted(sources_addrs_c))
        
        
        #if the search have been done before, look up the dictionary
        if (tree.addr, sources_addrs) in cls.naddrs_dict_tree_sources.keys():
            return cls.naddrs_dict_tree_sources[(tree.addr, sources_addrs)]
        
        #if not, initialize the entry in the dictionary
        networks_addrs = []
        cls.naddrs_dict_tree_sources[(tree.addr, sources_addrs)] = networks_addrs
        c_construction = False
        if (tree.addr, sources_addrs_c) not in cls.naddrs_dict_tree_sources.keys():
            c_construction = True
            networks_addrs_c = []
            cls.naddrs_dict_tree_sources[(tree.addr, sources_addrs_c)] = networks_addrs_c
            
        # base case I, if inputs_addrs only contain one address of the input,
        # and tree contains no child
        # i.e. the tree is the leaf vertex
        if len(sources_addrs) == 1 and tree.children_addrs == []:
            networks_addrs.append(sources_addrs[0])
            if c_construction:
                networks_addrs_c.append(cls.conj_addr(sources_addrs[0]))
            return cls.naddrs_dict_tree_sources[(tree.addr, sources_addrs)]
        
        #Base case II, if there is only one source
        if len(sources_addrs) == 1 and len(tree.children_addrs) == 1:
            if not cls.X0[sources_addrs[0]][0]: 
                # if the source is drive, it cannot be the leaf vertex of one 
                # or more delta node cascaded together. return []
                return cls.naddrs_dict_tree_sources[(tree.addr, sources_addrs)]

            #create a subnetwork output going out
            source_pos_addr = cls.positive_addr(sources_addrs[0])
            child_ntwk_addr = cls._from_tree_sources_unidir(Tree.at(tree.children_addrs[0]),
                                                      [source_pos_addr], even_case)
            
            network = cls.create(tree.addr, [child_ntwk_addr[0]], [source_pos_addr])
            
            # if the source is A*, return [], but the conjugate dict can be populated
            if sources_addrs[0] != source_pos_addr:
                if c_construction:
                    networks_addrs_c.append(network.addr)
            else:
                networks_addrs.append(network.addr)
            
            return cls.naddrs_dict_tree_sources[(tree.addr, sources_addrs)]
        
        #Base case III, top node in the tree is a delta node, the tree has multiple leaves
        if len(tree.children_addrs) == 1:
            
            #the child of a delta node should only have positive addr 
            if c_construction:
                #delete the key
                cls.naddrs_dict_tree_sources.pop((tree.addr, sources_addrs_c))

            child_ntwk_addr_list = cls._from_tree_sources_unidir(Tree.at(tree.children_addrs[0]),
                                                      list(sources_addrs), even_case)
                
            for child_ntwk_addr in child_ntwk_addr_list:
                network = cls.create(tree.addr, [child_ntwk_addr], list(sources_addrs))
                networks_addrs.append(network.addr)
                    
            return cls.naddrs_dict_tree_sources[(tree.addr, sources_addrs)]
            
        
        
        #the task is to generate all possible unique configurations to distribute 
        #sources_addrs into children_addrs[i] for all i, each containing 
        #children_leaves[i] number of leaves. Note that some sources_addrs elements
        #and children_addrs elements are unique.
        
        
        t_children_addrs = tree.children_addrs
        t_children_addrs = sorted(t_children_addrs)
        
        children_leaves = [tree.at(addr).leaves_count for addr in t_children_addrs]
        
        #combine children with the same addrs.
        previous_caddr = None
        new_children_leaves = [] #number of leaves in the each composite boxes(children)
        new_children_addrs = [] 
        for i, child_addr in enumerate(t_children_addrs):
            if child_addr != previous_caddr:
                new_children_addrs.append(child_addr)
                new_children_leaves.append(children_leaves[i])
            else:
                #if the last element is an addr
                if new_children_addrs[-1] == previous_caddr:
                    new_children_addrs[-1] = [previous_caddr,previous_caddr]
                else: #if the last element is a list
                    new_children_addrs[-1].append(previous_caddr)
                new_children_leaves[-1] += children_leaves[i]
            previous_caddr = child_addr
 
        #generate all configrations to distribute sources into the composite boxes          
        sources_configs_composite = slice_list_n(sources_addrs, new_children_leaves)
        
        for sources_config in sources_configs_composite:
            children_addrs_configs = []
            for i, child_sources in enumerate(sources_config):
                child_sources = list(child_sources)
                child_t_addr = new_children_addrs[i]
                if not isinstance(child_t_addr, list):
                    #if child_sources belong to one child
                    child_ntwk_addr_list_out = cls._from_tree_sources_unidir(Tree.at(child_t_addr),
                                                              child_sources, even_case)
                    child_ntwk_addr_list_in = cls._from_tree_sources_unidir(Tree.at(child_t_addr),
                                                                         cls.conj_addr(child_sources), even_case)
                    
                    child_ntwk_addr_list_in = cls.conj_addr(child_ntwk_addr_list_in)
                    child_ntwk_addr_list = child_ntwk_addr_list_out+child_ntwk_addr_list_in
                    child_ntwk_addr_list = list(set(child_ntwk_addr_list))
                    children_addrs_configs.append(child_ntwk_addr_list) 
                    if child_ntwk_addr_list == []:
                        break
                else:
                    #if child_sources belong to multiple children with same tree
                    #further distribute the soucese 
                    box_sources_configs = slice_list_n(child_sources, 
                                [int(len(child_sources)/len(child_t_addr))]*len(child_t_addr), True)
                    
                    box_addrs_configs_all = []
                    #go through each possible config
                    for box_sources_config in box_sources_configs:
                        box_sources_config = sorted(box_sources_config)
                        previous_config = None
                        
                        #group the same sources a child has
                        box_sources_config_grouped = []
                        for c_sources in box_sources_config:
                            if c_sources != previous_config:
                                box_sources_config_grouped.append([c_sources])
                                previous_config = c_sources
                            else:
                                box_sources_config_grouped[-1].append(c_sources)
                        
                        groups_addrs_configs = []
                        # go through each group of children 
                        for sources_group in box_sources_config_grouped:
                            child_ntwk_addr_list_out = cls._from_tree_sources_unidir(Tree.at(child_t_addr[0]),
                                                                      list(sources_group[0]), even_case)
                            child_ntwk_addr_list_in = cls._from_tree_sources_unidir(Tree.at(child_t_addr[0]),
                                                                    cls.conj_addr(list(sources_group[0])), even_case)
                            
                            child_ntwk_addr_list_in = cls.conj_addr(child_ntwk_addr_list_in)
                        
                            #list e.g. [(3,19), (3,23), ...]
                            child_ntwk_addr_list = child_ntwk_addr_list_out + child_ntwk_addr_list_in
                            child_ntwk_addr_list = list(set(child_ntwk_addr_list))
                            #each group find configurations of children_addrs where 
                            #children are in the sources_group 
                            groups_addrs_configs.append(itertools.combinations_with_replacement(
                                                    child_ntwk_addr_list,len(sources_group)))
                        
                        
                        #format [(((3,9),),((3,8),(3,19))), ...]
                        box_addrs_configs = list(itertools.product(*groups_addrs_configs))
                        box_addrs_configs_flat = []
                        for bac in box_addrs_configs:
                            bact = []
                            for baci in bac:
                                bact += list(baci)
                            box_addrs_configs_flat.append(bact)
                        #format [[(3,9),(3,8),(3,19)], ...]
                        
                        box_addrs_configs_all += box_addrs_configs_flat
                    children_addrs_configs.append(box_addrs_configs_all)
                    if box_addrs_configs_all == []:
                        break
                
                
            #tensor all possible ntwk_addrs of each child (children group)
            children_addrs_configs = list(itertools.product(*children_addrs_configs))
            
            for children_addrs_config in children_addrs_configs:
                children_addrs = []
                for cac in children_addrs_config:
                    if isinstance(cac, list):
                        children_addrs += cac
                    else:
                        children_addrs.append(cac)
                children_addrs = sorted(children_addrs)
                network = cls.create(tree.addr, children_addrs, list(sources_addrs))
                networks_addrs.append(network.addr)
                if c_construction:# and len(network.conj_addr(children_addrs))%2 == 1:
                    network_c = cls.create(tree.addr, cls.conj_addr(children_addrs), list(sources_addrs_c))
                    networks_addrs_c.append(network_c.addr)
                
        return cls.naddrs_dict_tree_sources[(tree.addr, sources_addrs)]
                

    

    #### miscellaneous

    @classmethod
    def at(cls, addrs):
        if type(addrs) is tuple:
            if addrs[1]<0:
                raise Exception("Network address can not be negative explicitly")
            return cls.all_networks[addrs[0]][addrs[1]]
        return [cls.at(addr) for addr in addrs]



    @classmethod
    def _children_at(cls, addrs):
        ''' return children addrs of a network(s) at addr(s). addr could be negative
        '''
        if addrs == None:
            return
        if type(addrs) is tuple:
            if addrs[1]> 0:
                return cls.at(addrs).children_addrs
            else:
                addrs = cls.conj_addr(addrs)
                return cls.conj_addr(Network.at(addrs).children_addrs)
        else:
            return [cls._children_at(addr) for addr in addrs]




    @classmethod
    def conj_addr(cls, addrs):
        '''
        returns conjugate address of an address
        '''
        if type(addrs) is tuple:
            return (addrs[0], -1*addrs[1])
        return [cls.conj_addr(addr) for addr in addrs]

    @classmethod
    def is_unique(cls, addrs, networks_addrs):
        for network_addr in networks_addrs:
            if Counter(addrs) == Counter(cls.at(network_addr).children_addrs):
                return False
        return True

    @classmethod
    def _source_names2addrs(cls, name):
        '''
        return address of sources
        '''
        if not isinstance(name, list):
            for i, (addr, source) in enumerate(cls.X0.items()):
                if source[1] == name:
                    return addr
            raise Exception("source %s not defined!"%name)
        else:
            return [cls._source_names2addrs(n) for n in name]


    def __str__(self, conj = False, offset = 0):
        if self.is_source:
            s_str = str(self.X0[self.sources_addrs[0]][1])
            if not conj:
                return str(offset)+s_str
            if conj:
                return str(offset)+s_str+'*'

        if conj:
            s = '->'
        else:
            s = '<-'

        s += str(offset)
        offset +=1
        if self.is_resonant:
            s += 'r'
        
        
        c = ''
        for child_addr in self.children_addrs:
            child_addr_ = self.positive_addr(child_addr)
            if child_addr[1] > 0:
                c += self.at(child_addr).__str__(conj, offset) + ','
            else:
                c += self.at(self.conj_addr(child_addr)).__str__(not conj, offset) + ','
            offset += self.at(child_addr_).node_number
        c = c[:-1]
        
        if len(self.children_addrs) == 1:
            s = s + 'd'
            if c[0] not in '-<':
                s = s + '-' + c
            else:
                s = s +c
        else:
            s = s+'[' + c+']'
        
        return s

    def __repr__(self):
        return self.__str__()+"@"+str(self.addr)

    def addr_at_node(self, n):
        """return the addr of the network at node n
        """
        if isinstance(n, list):
            return [self.node_at(ni) for ni in n]
        
        if not '_nodes_dict_' in self.__dict__:
            self._nodes_dict_ = {}

        if n in self._nodes_dict_:
            return self._nodes_dict_[n]

        if n == 0:
            self._nodes_dict_[n] = self.addr
            return self._nodes_dict_[n]

        if n > self.node_number:
            raise Exception("%d is larger than the number of nodes %d of network at %s"%(n, self.node_number, str(self.addr)))

        # firts node, the root, is passed
        counter = 1
        for child_addr in self.children_addrs:
            child_addr_ = self.positive_addr(child_addr)
            child_nodes = self.at(child_addr_).node_number
            if counter < n+1 and counter + child_nodes >= n+1:
                break
            counter += child_nodes

        if child_addr != child_addr_:
            self._nodes_dict_[n] = self.conj_addr(self.at(child_addr_).addr_at_node(n - counter))
        else:
            self._nodes_dict_[n] = self.at(child_addr_).addr_at_node(n - counter)
        return self._nodes_dict_[n]

    def at_node(self,n):
        addr = self.addr_at_node(n)
        pos_addr = self.positive_addr(addr)
        return self.at(pos_addr)

    def extend_node(self, node):
        ''' 
        take in a node number and translate to the full node representation
        '''
        # print(node)
        counter = 1
        if node == 0: return (0, 0)
        
        for child_addr in self.children_addrs:
            if counter == node: return (0, counter)
            child_addr_pos = self.positive_addr(child_addr)
            child = self.at(child_addr_pos)
            # print(child)
            if counter + child.node_number > node:
                return (0, nd_al.offset(child.extend_node(node-counter), counter))
            counter += child.node_number
        

    def extend_nodes(self, nodes):
        # extend all the nodes and add them to one tuple
        
        nodes = [self.extend_node(node) for node in nodes]
        if len(nodes) == 0: return ()
        nodei = nodes[0]
        for node in nodes[1:]:
            nodei = nd_al.add(nodei, node)

        return nodei

    @property
    def node_number(self):
        '''
        return the number of node including the root one

        '''
        if '_node_number' in self.__dict__.keys():
            return self._node_number
        self._node_number = Tree.at(self.taddr).node_number 
        return self._node_number
        

    @property
    def resonant_nodes(self):
        '''
        for converntion, the root node 0 is not included no matter resonant or not.
        This info can be easily accessed by self.is_resonant. 
                
        '''
        if '_resonant_nodes' in self.__dict__.keys():
            return self._resonant_nodes

        resonant_nodes = []

        counter = 1
        for child_addr in self.children_addrs:
            child_addr = self.positive_addr(child_addr)
            child = self.at(child_addr)
            if child.is_resonant and not child.is_source:
                resonant_nodes.append(counter)
            if child.resonant_nodes != []:
                resonant_nodes += list(nd_al.offset(child.resonant_nodes, counter))
            counter += self.at(child_addr).node_number
        self._resonant_nodes = resonant_nodes
        return self._resonant_nodes
    
    @property
    def internal_nodes(self):
        '''
        for converntion, the root node 0 is not included.        
        '''
        if '_internal_nodes' in self.__dict__.keys():
            return self._internal_nodes

        internal_nodes = []

        counter = 1
        for child_addr in self.children_addrs:
            child_addr = self.positive_addr(child_addr)
            child = self.at(child_addr)
            if  not child.is_source:
                internal_nodes.append(counter)
            internal_nodes += list(nd_al.offset(child.internal_nodes, counter))
            counter += self.at(child_addr).node_number
        self._internal_nodes = internal_nodes
        return self._internal_nodes
    
    @classmethod
    def positive_addr(cls, addr):
        if addr[1]<0:
            return cls.conj_addr(addr)
        return addr
    
    #### evaluation wrapper function

    def expression(self):
        '''
        a wrapper function
        return the expression of the network by treating it as a $Rot(\eta)$
        or a $\partial_{A^*}K$ network. 

        Returns
        -------
        TYPE
            DESCRIPTION.

        '''
        husimi_network = self.with_bond_at()
        
        if self.is_resonant:
            prefactors = husimi_network.prefactors_dAsK()
        else:
            prefactors =  husimi_network.prefactors_virtual()
            
        expression = 0
        for bonds in prefactors:
            expression += prefactors[bonds][0]*self.sources_prod(bonds)
            
        return expression
            
    
    def sources_prod(self, bonds):
        p = 1
        for addr in self.sources_addrs:
            p *= self.X0[addr][1]
        
        p /= self.modes[0][0]**bonds*self.modes[0][1]**bonds
        p *= self.commutator**bonds
        
        return p
        
    
    def with_bond_at(self, bond_nodes = []):
        if "_husimi_networks" not in self.__dict__.keys():
            self._husimi_networks = {}
        bond_nodes = tuple(sorted(bond_nodes))
        if bond_nodes not in self._husimi_networks.keys():
            self._husimi_networks[bond_nodes] = HusimiNetwork(self, bond_nodes)
        return self._husimi_networks[bond_nodes] 
        
        
    #### node removing
    
    
    def separate_nodes_from(self, nodes, node):
        upper_nodes = []
        lower_nodes = []
        node_number = self.at_node(node).node_number
        for n in nodes:
            if n < node:
                upper_nodes.append(n)
            elif n > node and n < node + node_number:
                lower_nodes.append(n-node)
            elif n == node and node_number == 1:
                lower_nodes.append(n-node)
            else:
                upper_nodes.append(n-node_number+1)
        return upper_nodes, lower_nodes
    
    
    def remove(self, nodes, nodes_map = {}):
        '''
            

        Parameters
        ----------
        nodes : TYPE
            DESCRIPTION.
        nodes_map: dict
            key is the node index of each node in self, 
            entry is the node index, in a new set, that the key is mapped to
            
            
        Returns
        -------
        None.

        '''
        nodes_map0 = {}
        for i in range(self.node_number):
            nodes_map0[i] = i
        
        if nodes_map == {}:
            nodes_map = nodes_map0.copy()
            # for i in range(self.node_number):
                # nodes_map[i] = i
        
        if nodes == []:
            return self, nodes_map
        
        if '_remove_node_dict' not in self.__dict__.keys():
            self._remove_node_dict = {}
        
        node0 = nodes[0]
        
        child_nodes_list = []
        
        if node0 in self._remove_node_dict:
            ntwk, new_nodes_map0 = self._remove_node_dict[node0]
        else:
            tree = Tree.at(self.taddr).remove(node0)
        
        
            # find the source list of ntwk
            source_addrs = self.sources_addrs.copy()
            rmvd_network = self.at_node(node0)
            rmvd_source_addrs = rmvd_network.sources_addrs
            
            direction = 1
            if self.addr_at_node(node0) != rmvd_network.addr:
                direction = -1
            #TODO: multimode
            source_addrs += [(0, direction)]
                
            for item in rmvd_source_addrs:
                if direction == 1:
                    source_addrs.remove(item)
                else:
                    source_addrs.remove(self.conj_addr(item))
                
            source_addrs = tuple(sorted(source_addrs))
            
            # find the children of ntwk
            children_addrs = []
            counter = 1
            for child_addr in self.children_addrs:
                # get the child network
                child_direction = 1
                child_addr_pos = self.positive_addr(child_addr)
                if child_addr_pos != child_addr:
                    child_direction = -1
                child = self.at(child_addr_pos)
                if node0 == counter: 
                    #if the child is removed
                    children_addrs += [(0, direction)]
                    cnl = [counter]
                elif node0 > counter and node0 < counter + child.node_number:
                    # a node in the child is removed
                    c_nodes_map = {}
                    for key in range(child.node_number):
                        c_nodes_map[key] = key + counter
                    new_child, c_nodes_map = child.remove([node0-counter],c_nodes_map)
                    if child_direction == 1:
                        children_addrs += [new_child.addr]
                    else:
                        children_addrs += [self.conj_addr(new_child.addr)]
                    cnl = []
                    for i in range(new_child.node_number):
                          cnl.append(c_nodes_map[i])
                else:
                    # if the child is the same. 
                    children_addrs += [child_addr]
                    cnl = []
                    for i in range(child.node_number):
                        cnl.append(i+counter)
                child_nodes_list.append(cnl)
                counter += child.node_number

                
            
            new_nodes_map0 = {0:0}
            ntwk_list = self._from_tree_sources_unidir(tree, source_addrs,
                                                               self.is_even)
            for ntwk_pos in ntwk_list:
                if Counter(children_addrs) == Counter(self.at(ntwk_pos).children_addrs):
                    
                    
                    # construct the node map of ntwk
                    index_map = index_mapping(children_addrs,self.at(ntwk_pos).children_addrs) 
                    new_child_nodes_list = []
                    for i in index_map:
                        new_child_nodes_list += child_nodes_list[i]
                    
                    for i, key in enumerate(new_child_nodes_list):
                       new_nodes_map0[i+1] = nodes_map0[key]
        
                    self._remove_node_dict[node0] = self.at(ntwk_pos), new_nodes_map0
                    ntwk , _ = self._remove_node_dict[node0]
                    
                    break
                
        new_nodes_map = {0:0}
        for key in new_nodes_map0:
            new_nodes_map[key] = nodes_map[new_nodes_map0[key]]
            
        new_nodes, _ = self.separate_nodes_from(nodes[1:], node0)
        return ntwk.remove(new_nodes,new_nodes_map)
        
        
    
        

class HusimiNetwork(Network):
    # a network with some of its $A, A^*$ leaf vertices labeld by 
    def __init__(self, network, bond_nodes):
        self.network = network
        self.bond_nodes = bond_nodes
        self._construct_children_addrs()
        
    def _construct_children_addrs(self):
        '''
        construct self.children_addrs = [(network1, bond_nodes1,direction1), 
                                         (network2, bond_nodes2, direction2),...]
        
        direction is 1 or -1, denote the direction of the child's output.
        Returns
        -------
        None.

        '''
        children_addrs = []
        counter = 1
        for child_addr in self.network.children_addrs:
            pos_addr = self.network.positive_addr(child_addr)
            directionality = 1
            if pos_addr != child_addr:
                directionality = -1
            child_hntwk = self.at_node(counter) 
            counter += child_hntwk.node_number
            children_addrs.append((child_hntwk.network.addr, child_hntwk.bond_nodes, directionality))
        self.children_addrs = children_addrs
        return 
        
        
    #### miscellaneous
    
    
    
        
    @classmethod
    def at(cls, addr):
        return Network.at(addr[0]).with_bond_at(addr[1])
        
    
    @property
    def propag(self):
    # only makes sense if the network is a virtual excitation
#        if self.children_addrs == []:
        if '_propag' in self.__dict__.keys():
            return self._propag
        if self.network.is_source or self.is_resonant:
            self._propag = 1
        else:
            self._propag = 1 / (self.freq - self.network.X0[(0, 1)][2])

        return self._propag
    
    @property 
    def node_number(self):
        return self.network.node_number
    
    @property
    def freq(self):
        return self.network.freq
    
    @property 
    def resonant_nodes(self):
        return self.network.resonant_nodes
    
    @property 
    def internal_nodes(self):
        return self.network.internal_nodes

    @property 
    def is_resonant(self):
        return self.network.is_resonant    
    
    def at_node(self, node):
        if node == 0:
            return self
        if "_node_dict" not in self.__dict__.keys():
            self._node_dict = {}
        
        if node in self._node_dict:
            return self._node_dict[node]
        
        _, new_bond_nodes = self.network.separate_nodes_from(self.bond_nodes, node)
        
        self._node_dict[node] = self.network.at_node(node).with_bond_at(new_bond_nodes)
    
        return self._node_dict[node]
    
    def addr_at_node(self, node):
        direction = 1
        node_naddr = self.network.addr_at_node(node)
        if node_naddr == self.network.positive_addr(node_naddr):
            direction = -1
        return (self.at_node(node).network.addr, self.at_node(node).bond_nodes, direction)
    
    
    @property
    def sources_addrs(self):
        return self.network.sources_addrs

    def __str__(self, conj = False, offset = 0):
        if self.network.is_source:
            s_str = str(self.network.X0[self.sources_addrs[0]][1])
            s = ''
            if not conj:
                s+= str(offset)+s_str
            if conj:
                s+= str(offset)+s_str+'*'
            if 0 in self.bond_nodes:
                s+='-'
            return s

        if conj:
            s = '->'
        else:
            s = '<-'

        s += str(offset)
        offset +=1
        if self.is_resonant:
            s += 'r'
        
        
        c = ''
        for child_addr in self.children_addrs:
            if child_addr[2] > 0:
                c += self.at(child_addr).__str__(conj, offset) + ','
            else:
                c += self.at(child_addr).__str__(not conj, offset) + ','
            offset += self.at(child_addr).node_number
        c = c[:-1]
        
        if len(self.children_addrs) == 1:
            s = s + 'd'
            if c[0] not in '-<':
                s = s + '-' + c
            else:
                s = s +c
        else:
            s = s+'[' + c+']'
        
        return s
        

    def __repr__(self):
        return self.__str__()+"@"+'('+str(self.network.addr)+',' +str(self.bond_nodes)+')'
    
    
    
    #### evaluations
    
    
    def prefactors_input(self, conj=False):
        '''
        a wrapper function
        return the dictionary of preactors of the network by treating it as 
        a $Rot(\eta)$ or a $A+Sta(\eta)$ or xi network

        Returns
        -------
        TYPE
            DESCRIPTION.

        '''
                
        if self.is_resonant:
            if len(self.children_addrs) == 0: # if just a source
                return self.prefactors_no_top_dressing(conj)
            return self.prefactors_exponential(conj) # if Sta(\eta) network
        else:
            return self.prefactors_virtual(conj)
        
        
    #### main evaluation functions

    def prefactors_dAsK(self, conj=False):
        '''
        return the dictionary of preactors of the network by treating it as a 
        $\partial_{A^*}K$ network

        Returns (permutation_factor, operator_powers), operator_powers = [[m, n]]
        A^m A^*n
        -------
        TYPE
            DESCRIPTION.

        '''
        if "_prefactors_dAsK" in self.__dict__.keys():
            if conj:
                return self._prefactors_dAsK_conj.copy()
            else:                
                return self._prefactors_dAsK.copy()
        
        # no top Sta(\eta) term
        prefactors = self.prefactors_no_top_dressing()
        
        resonant_nodes = []
        for node in self._generate_unordered_dressers(self.resonant_nodes):
            if len(node) == 1:
                resonant_nodes.append(node[0])
                
        # if resonant_nodes != self.resonant_nodes:
            # print(self,resonant_nodes,self.resonant_nodes)
        
        # if self.network.taddr in [17,18,20,21]:
            # prefactors = {0:(0,[[0,0]])}
            
        
        for node in resonant_nodes:
            # continue
            # loop through each possible break point of top Sta(eta) term
            top_sta_eta = self.remove([node])
            
            # if len(top_sta_eta.internal_nodes)!=2:
                # continue
            
            bottom_dAsk = self.at_node(node)
            bottom_naddr = self.network.addr_at_node(node)
            
            bottom_addr_abs = self.network.positive_addr(bottom_naddr)
            direction = 1
            if bottom_addr_abs == bottom_naddr:
                direction = -1
                previous_factors_ops = star_factor_ops(top_sta_eta.prefactors_exponential(),
                                                       bottom_dAsk.prefactors_dAsK(False),1)
                # previous_factors_ops = {0:(0,[[0,0]])}
            else:
                previous_factors_ops = star_factor_ops(bottom_dAsk.prefactors_dAsK(True),
                                                       top_sta_eta.prefactors_exponential(),1)
            
                # previous_factors_ops = top_sta_eta.prefactors_exponential()
                # print(top_sta_eta,top_sta_eta.network.addr,  previous_factors_ops[0][0])
                # print(top_sta_eta.network.with_bond_at().prefactors_exponential()[0][0])
                
            for i, (key, factor_ops) in enumerate(previous_factors_ops.items()):
                if (not key in prefactors) and factor_ops[0]!=0: 
                    prefactors[key] = (0,factor_ops[1])
                    
                if factor_ops[0]!=0:
                    pf = prefactors[key][0] + factor_ops[0]*direction
                    
                    prefactors[key] = (pf.expand(numr=True), factor_ops[1]) 

        # construct the conjuage diagram.
        self._prefactors_dAsK = prefactors
        prefactors_conj = {}
        for i, (key, factor_ops) in enumerate(prefactors.items()):
            prefactors_conj[key] = (factor_ops[0], self.ops_conj(factor_ops[1]))
            
        self._prefactors_dAsK_conj = prefactors_conj
        if conj:
            return self._prefactors_dAsK_conj.copy()
        else:
            return self._prefactors_dAsK.copy()
    
    
    #### computing the network with no dressing to top node
    

    
    def prefactors_no_top_dressing(self, conj = False):
        '''
        evaluate the dictionary of preactors such that no network is dressing 
        the top output.
        in resonant case, means that the network is in the dressed $\partial_{A^*s}K$.
        in the off-resonant case, means that the propagator at top is not dressed

        Returns (permutation_factor, operator_powers), operator_powers = [[m, n]]
        -------
        None.

        '''
        
        if "_prefactors_no_top_dressing" in self.__dict__.keys():
            if conj:
                return self._prefactors_no_top_dressing_conj.copy()
            else:
                return self._prefactors_no_top_dressing.copy()
              
        self._prefactors_no_top_dressing = {0:(0,[[0,0]])}
        self._prefactors_no_top_dressing_conj = {0:(0,[[0,0]])}
        
        #base case, if just a source
        if len(self.children_addrs) == 0: 
            power = [[0,0]]*self.modes_number
            s = self.X0[self.sources_addrs[0]]
            if s[0] and 0 not in self.bond_nodes:
                power[s[3]][0] = 1
            prefactors = {0:(1,power)}
        else:
            prefactors = {0:(0,[[0,0]])}
            
            
        #base case: need to check if is a valid diagram.
        # if the network is off-resonant, then its validity depends on its child. 
        # if the network is resonant, the  it cannot be a delta diagram unless 
        # the child is an incoming oscillato excitation
        if self.is_resonant and len(self.children_addrs)==1\
            and self.children_addrs[0][0].addr != (0,1):
                return self._prefactors_no_top_dressing.copy()
        
        
        
        # base case: if any child is not a valid input
        for child_addr in self.children_addrs:
            child = self.at(child_addr)
            child_prefactors =  child.prefactors_input(child_addr[2]==-1)
            if child_prefactors[0][0] == 0: # classical component is zero
                return self._prefactors_no_top_dressing.copy()
        
            
        # recursive case
        children_permuted = self.children_permuted
        for children_addrs in children_permuted:
            # TODO: multimode
            previous_factors_ops = {0:(1,[[0,0]])}
            for child_addr in children_addrs:
                child = self.at(child_addr)
                permutation_factors_ops = child.prefactors_input(child_addr[2] == -1)
                previous_factors_ops = star_factor_ops(previous_factors_ops, permutation_factors_ops)
                if previous_factors_ops[0][0] == 0:
                    break
                
            for i, (key, factor_ops) in enumerate(previous_factors_ops.items()):
                #TODO multimode. delta term depends on propagator
                if (not key in prefactors) and factor_ops[0]!=0: 
                    prefactors[key] = (0,factor_ops[1])
                    
                if factor_ops[0]!=0:
                    pf = prefactors[key][0]\
                        +factor_ops[0]*self.multiplicity_from_bonds*self.propag*self.mixing_strength
                    
                    prefactors[key] = (pf.expand(numr=True), factor_ops[1])
            


        # construct the conjuage diagram.
        self._prefactors_no_top_dressing = prefactors
        prefactors_conj = {}
        for i, (key, factor_ops) in enumerate(prefactors.items()):
            prefactors_conj[key] = (factor_ops[0], self.ops_conj(factor_ops[1]))
        self._prefactors_no_top_dressing_conj = prefactors_conj
            
        if conj:
            return self._prefactors_no_top_dressing_conj.copy()
        else:
            return self._prefactors_no_top_dressing.copy()
    
    @property
    def multiplicity_from_bonds(self):
        '''
        for a child of the top node contain a leaf vertex in bond_nodes, then 
        the child should be treated as a unique one even if it is the same as 
        another child. the property children_permuted does not contain multiplicity
        and this function compensate it.

        Returns
        -------
        None.

        '''
        
        children_addrs_set = set(self.children_addrs)
        factor = 1
        
        for child_addr in children_addrs_set:
            if child_addr[1]!=():
                c = self.children_addrs.count(child_addr)
                factor *= math.factorial(c)
        
        return factor
    
    @property
    def mixing_strength(self):
        if '_mixing_strength' in self.__dict__:
            return self._mixing_strength
        i = len(self.children_addrs)
        if i == 0:
            self._mixing_strength  = 1
        elif i == 1:
            self._mixing_strength = self.mixers.get(i+1, Symbol('\delta'))
        else:
            self._mixing_strength = self.mixers.get(i+1, Symbol(f'g_{i+1}'))
        return self._mixing_strength
    
    
    @property
    def children_permuted(self):
        if '_children_permuted' in self.__dict__:
            return self._children_permuted
                
        self._children_permuted = \
            list(distinct_permutations(self.children_addrs))
        if self._children_permuted == [()]:
            self._children_permuted = []
            
        return self._children_permuted
    
    
    
    #### compute vitrual excitation network
    
    
    def prefactors_virtual(self, conj = False):
        '''
        return the dictionary of preactors of the network by treating it as a 
        $Rot(\eta)$ network
        
        Returns (permutation_factor, operator_powers), operator_powers = [[m, n]]
        -------
        TYPE
            DESCRIPTION.

        '''
        
        if "_prefactors_virtual" in self.__dict__.keys():
            # if self.network.addr == (5,12):
               # print('here')
               # print(self._prefactors_virtual)
            if conj:
                return self._prefactors_virtual_conj
            else:
                return self._prefactors_virtual.copy()
            
            
        self._prefactors_virtual = {0:(0,[[0,0]])}
        self._prefactors_virtual_conj = {0:(0,[[0,0]])}
        
        if self.is_resonant:
            return self._prefactors_virtual.copy()
        
    
        # dressing_nodes_configs = all_combinations(self.resonant_nodes)
        dressing_nodes_configs = self._generate_unordered_dressers(self.resonant_nodes)

        prefactors = {0:(0,[[0,0]])}
        
        #loop through all possible 
        for dressing_nodes in dressing_nodes_configs:
            # if self.network.taddr == 12 and dressing_nodes ==[]:
                # print(dressing_nodes)
                # continue
            bare_virtual = self.remove(dressing_nodes)
                        
            #base case: bare_virtual is invalid.
            if bare_virtual.prefactors_no_top_dressing()[0][0] == 0:
                continue
            
            dresser_dict = self.get_dresser_dict(dressing_nodes)
            
            overcounting = self.get_overcounting(dressing_nodes)
            
            
            valid = True
            #base case: dresser is invalid. always valid?
            for node, dresser in dresser_dict.items():
                if dresser.prefactors_dAsK()[0][0] == 0:
                    valid = False
                    break
            if not valid:
                continue
                
            extended_dressing_nodes = self.network.extend_nodes(dressing_nodes)
            ordered_dressing_nodes_configs = self._generate_ordered_dressers(extended_dressing_nodes)
            
            for ordered_dressing_nodes in ordered_dressing_nodes_configs:
                previous_factors_ops = bare_virtual.prefactors_no_top_dressing()
                direction = 1
                for dressing_node in ordered_dressing_nodes:
                    dresser = dresser_dict[dressing_node]
                    node_naddr = self.network.addr_at_node(dressing_node)
                    if node_naddr == Network.positive_addr(node_naddr):
                        direction*=-1
                        dresser_prefactors = dresser.prefactors_dAsK()
                        previous_factors_ops = star_factor_ops(previous_factors_ops, 
                                                               dresser_prefactors,1)
                    else:
                        dresser_prefactors = dresser.prefactors_dAsK(conj = True)
                        previous_factors_ops = star_factor_ops(dresser_prefactors,
                                                               previous_factors_ops,1)
                    
                for i, (key, factor_ops) in enumerate(previous_factors_ops.items()):
                    #TODO multimode. delta term depends on propagator
                    if (not key in prefactors) and factor_ops[0]!=0: 
                        prefactors[key] = (0,factor_ops[1])
                        
                    if factor_ops[0]!=0:
                        pf = prefactors[key][0]\
                            +factor_ops[0]*direction\
                                *self.propag**len(ordered_dressing_nodes)/overcounting
                        
                        prefactors[key] = (pf.expand(numr=True), factor_ops[1]) 
                    
            
            # construct the conjuage diagram.
        self._prefactors_virtual = prefactors
        prefactors_conj = {}
        for i, (key, factor_ops) in enumerate(prefactors.items()):
            prefactors_conj[key] = (factor_ops[0], self.ops_conj(factor_ops[1]))
        
        self._prefactors_virtual_conj = prefactors_conj
        
        if conj:
            return self._prefactors_virtual_conj.copy()
        else:
            return self._prefactors_virtual.copy()


    def get_dresser_dict(self, dressing_nodes):
        '''
        return a dictionary. key is the node number that is the start of a dresser,
        entry is a HusimiNetwork instance. 

        Parameters
        ----------
        dressing_nodes : TYPE
            DESCRIPTION.

        Returns
        -------
        None.

        '''
        dresser_dict = {}
        for dressing_node in dressing_nodes:
            hntwk = self.at_node(dressing_node)
            _, new_dressing_nodes = self.network.separate_nodes_from(dressing_nodes, dressing_node)
            dresser_dict[dressing_node] = hntwk.remove(new_dressing_nodes)
        
        return dresser_dict

    @classmethod
    def _generate_ordered_dressers(cls, dressing_nodes):
        '''
        RULE: child dresser comes after the parent dresser
        dressing_nodes 
        '''


        if (len(dressing_nodes) == 2 and dressing_nodes[1] == -1) or len(dressing_nodes)==0:
            return [()]

        dressing_nodes = list(dressing_nodes)
        
        int_list = []

        #the child of the child is a dressing node
        tuple_list = []

        #seperate the nodes into two list
        for i, item in enumerate(dressing_nodes[1:]):
            if isinstance(item, int):
                int_list.append(item)
            else:
                tuple_list.append(item)

        nodes_configs = list(itertools.permutations(int_list, len(int_list)))
        for child_tuple in tuple_list:
            child_tuple = list(child_tuple)
            child_configs = cls._generate_ordered_dressers(child_tuple)
            new_nodes_configs = []
            for nodes_config in nodes_configs:
                nodes_config = list(nodes_config)
                if child_tuple[0] in nodes_config:
                    start = nodes_config.index(child_tuple[0])+1
                else:
                    start = 0
                for child_config in child_configs:
                    combined_configs = combine(nodes_config[start:], child_config)
                    for combined_config in combined_configs:
                        new_nodes_configs.append(nodes_config[:start] +combined_config)
            nodes_configs = new_nodes_configs

        return nodes_configs



    
    #### computing network from exponential map
    
    def prefactors_exponential(self, conj = False):
        '''
        return the dictionary of preactors of the network by treating it as a 
        term in the expansion of $Sta(eta)$ or $i\patial_{A^*}S$.

        Returns
        -------
        None.

        '''
        if "_prefactors_exponential" in self.__dict__.keys():
            if conj:
                return self._prefactors_exponential_conj.copy()
            else:
                return self._prefactors_exponential.copy()
            
        self._prefactors_exponential = {0:(0,[[0,0]])}
        self._prefactors_exponential_conj = {0:(0,[[0,0]])}
        
        # return self._prefactors_exponential
        
            
        dressing_nodes_configs = self._generate_unordered_dressers(self.internal_nodes)
        
        dressing_nodes_configs.remove([])
        prefactors = self.prefactors_virtual()
        
        directionality = 1
        if not self.is_resonant:
            directionality = -1
        
        # loop through each possible combination of the dressing nodes
        for dressing_nodes in dressing_nodes_configs:
            
            first_dresser = self.remove(dressing_nodes)
            
            #base case: the first dresser in is invalid. first dresser needs to be off-resonant.
            if first_dresser.is_resonant or first_dresser.prefactors_exponential()[0][0] == 0:
                continue
            
            dresser_dict = self.get_dresser_dict(dressing_nodes)
            overcounting = self.get_overcounting(dressing_nodes)

            invalid_dresser = False
            #base case: dresser is invalid. 
            for node, dresser in dresser_dict.items():
                if dresser.is_resonant or dresser.prefactors_exponential()[0][0] == 0:
                    invalid_dresser = True
                    break
            if invalid_dresser:
                continue
                
            extended_dressing_nodes = self.network.extend_nodes(dressing_nodes)
            ordered_dressing_nodes_configs = self._generate_ordered_dressers(extended_dressing_nodes)
            
            for ordered_dressing_nodes in ordered_dressing_nodes_configs:
                previous_factors_ops = first_dresser.prefactors_exponential()
                for dressing_node in ordered_dressing_nodes:
                    dresser = dresser_dict[dressing_node]
                    node_naddr = self.network.addr_at_node(dressing_node)
                    if node_naddr == Network.positive_addr(node_naddr):
                        dresser_prefactors = dresser.prefactors_exponential()
                        previous_factors_ops = star_factor_ops(previous_factors_ops, 
                                                               dresser_prefactors,1)
                    else:
                        dresser_prefactors = dresser.prefactors_exponential(conj = True)
                        previous_factors_ops = star_factor_ops(dresser_prefactors,
                                                               previous_factors_ops,1)
                    
                for i, (key, factor_ops) in enumerate(previous_factors_ops.items()):
                    #TODO multimode. delta term depends on propagator
                    if (not key in prefactors) and factor_ops[0]!=0: 
                        prefactors[key] = (0,factor_ops[1])
                    
                    if factor_ops[0]!=0:
                        pf = prefactors[key][0]\
                            +factor_ops[0]*directionality\
                                /math.factorial(len(dressing_nodes)+1)/overcounting
                        
                        prefactors[key] = (pf.expand(numr=True), factor_ops[1]) 
                    
        
        # construct the conjuage diagram.
        self._prefactors_exponential = prefactors
        prefactors_conj = {}
        for i, (key, factor_ops) in enumerate(prefactors.items()):
            prefactors_conj[key] = (factor_ops[0], self.ops_conj(factor_ops[1]))
            
        self._prefactors_exponential_conj = prefactors_conj
        
        if conj:
            return self._prefactors_exponential_conj.copy()
        else:
            return self._prefactors_exponential.copy()
        
    
    
    
    #### evaluation tools
    
    
    def ops_conj(self, ops):
        '''
        return the conjugate of a operator powers tuple. i.e. [[m,n]] -> [[n,m]]

        Parameters
        ----------
        ops : TYPE
            DESCRIPTION.

        Returns
        -------
        power : TYPE
            DESCRIPTION.

        '''
        power = [[0,0]]*self.modes_number
        for i, p in enumerate(ops):
            power[i] = p[::-1]
            
        return power
        
     
    #### node removing
    
    def remove(self, remove_nodes):
        '''

        Parameters
        ----------
        node : list
            DESCRIPTION.

        Returns HusimiNetwork instance
        -------
        None.

        '''
        if remove_nodes == []:
            return self
        
        ntwk, nodes_map = self.network.remove(remove_nodes)
        
        
        
        bond_nodes = list(self.bond_nodes) + remove_nodes
        new_bond_nodes = []
        for node in bond_nodes:
            for key, value in nodes_map.items():
                if value == node:
                    new_bond_nodes.append(key)
                    break
        
        return ntwk.with_bond_at(new_bond_nodes)
        

    def node_footprint(self, node):
        '''
        generate the footprint of a node. two nodes with the same footprint 
        are interchangeble. 
        e.g.
        <-0r[1A,2A,<-3[4A,->5r[6A,7A*,8A*],->9 r[10A,11A*,12A*]],
             <-13[14A,->15r[16A,17A*,18A*],->19r[20A,21A*,22A*]]]
        node 5, 9, 15, 19 have the same footprint.
        
        Parameters
        ----------
        node : TYPE
            DESCRIPTION.

        Returns
        -------
        None.

        '''
        
        ancestors = nd_al.ancestors(self.network.extend_node(node))
        footprint = []
        for ancestor in ancestors:
            footprint.append(self.addr_at_node(ancestor))
        footprint.append(self.addr_at_node(node))
        
        return tuple(footprint)
    
    def footprint(self, dressing_nodes):
        '''
        return a footprint of the HusimiNetwork with the dressing_nodes specified.

        Parameters
        ----------
        dressing_nodes : TYPE
            DESCRIPTION.

        Returns
        -------
        None.

        '''
        #TODO save in dictionary
        counter = 1
        footprint = []
        for child_addr in self.children_addrs:
            child = self.at_node(counter)
            if len(child.children_addrs) == 0:
                child_footprint = (child_addr[0], child_addr[2], child_addr[1])
            else:            
                dressing = 0
                if counter in dressing_nodes:
                    dressing = 1
                _, child_dressing_nodes = self.separate_nodes_from(dressing_nodes, counter)
                child_footprint = (child_addr[0], child_addr[2], dressing, 
                                   child.footprint(child_dressing_nodes))
            
            footprint.append(child_footprint)
            counter += child.node_number
            
        return tuple(sorted(footprint))
    
    def _generate_unordered_dressers(self, available_dressing_nodes):
        configs = all_combinations(available_dressing_nodes)
        configs_dict = {}
        for dressing_nodes in configs:
            footprint = self.footprint(dressing_nodes)
            if footprint not in configs_dict:
                configs_dict[footprint] = dressing_nodes
        return list(configs_dict.values())
        
    
    
    def get_overcounting(self, dressers):
        '''
        when computing the permutation factor in virtual excitation, each bond_node
        is treated as unique. This assumption overcounts the bonds that connect to 
        the same dresser. This function compute such overcounting factor

        Parameters
        ----------
        nodes : TYPE
            DESCRIPTION.
        escape_bond : list
            contain the bond_node 

        Returns
        -------
        None.

        '''
        overcounting = 1
        for node in [0]+self.internal_nodes:
            
            child = self.at_node(node)
            
            _, bottom_dressers = self.separate_nodes_from(dressers,node)
            overcounting *= child._get_overcounting_top_node(bottom_dressers)
                    
                
        
        
        return overcounting
    
    
    def _get_overcounting_top_node(self, dressing_nodes):
        if len(dressing_nodes) == 0:
            return 1
        counter = 1
        child_footprints = []
        for child_addr in self.children_addrs:
            child = self.at_node(counter)
            _, child_dressing_nodes = self.separate_nodes_from(dressing_nodes, counter)
            child_footprint = (child_addr[0], child_addr[2], 
                               child.footprint(child_dressing_nodes))
            if len(child_dressing_nodes) != 0 or counter in dressing_nodes:
                if len(child.bond_nodes)==0:
                    child_footprints.append(child_footprint)
                
            counter += child.node_number

        dressed_child_dict = Counter(child_footprints)
        overcounting = 1
        for i in dressed_child_dict.values():
            overcounting *= math.factorial(i)
        return overcounting
            
            
    
            
            
            
            
            

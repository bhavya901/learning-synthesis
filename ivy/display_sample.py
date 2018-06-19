import networkx as nx
import matplotlib.pyplot as plot
import learnInvariant as li

node_shape = 'so^>v<dph8' # s for square, o for circle etc.
node_color = ['white', 'r', 'g', 'y', 'b', 'brown', 'purple', 'black', 'orange']  # can support 3 unary relation and 8 binary relations
# a fixed colour scheme is used for predictability of state of a node

def getGraph(unv, interp):
	global node_shape, node_color
	ax = plot.gca()
	ax.collections[0].set_edgecolor("#000000")
	i = 0 
	g = nx.MultiGraph()
	for sort in unv.keys():  # adding nodes
		attr = {'sort': sort, 'shape' = node_shape[i], 'cnum' = 0} # cnum is color number, <TODO> use colormap to support more than 3 unary relation
		for const in unv[sort]:
			g.add_node((str(const),attr))
		i+=1

	unary_relOrder = {}
	bin_relOrder = {}
	for key, value in interp.valof: # adding edges and colouring nodes
		if isinstance(key, li.Function):
			arity = key.arity() if key.sort=='bool' else key.arity()+1
			if arity>=3:
				continue
			name, retsort = key.name, key.sort
			argsort = tuple([arg.sort for arg in key.args])	
			tup = (name, argsort, retsort)
			nodes = [str(arg) for arg in key.args]
			if arity==1: #color node
				if tup in unary_relOrder:
					num = unary_relOrder[tup]
				else:
					num = len(unary_relOrder)
					unary_relOrder[tup] = num
				g.nodes[nodes[0]]['cnum'] = g.nodes[nodes[0]]['cnum'] +2**num/8.0
			else: # add edge
				if tup in bin_relOrder:
					num = bin_relOrder[tup]
				else:
					num = len(bin_relOrder)
					bin_relOrder[tup] = num
				if retsort=='bool' and value.val=='0':
					continue
				if retsort!='bool':
					nodes.append(str(value))
				attr = {'color' : node_color[num+1], 'rel_name' : name, 'cnum' : (num+1)/8.0}
				g.add_edge((nodes[0], nodes[1], attr))
	
	for node in g.nodes():
		cnum = g.nodes[node]['cnum']*8
		g.nodes[node]['color'] = node_color[cnum]

	return g
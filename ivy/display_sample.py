import networkx as nx
import matplotlib.pyplot as plot
import learnInvariant as li
from networkx.drawing.nx_agraph import graphviz_layout

nshape = 'os^>v<dph8' # s for square, o for circle etc.
node_color = ['white', 'r', 'g', 'y', 'b', 'brown', 'purple', 'black', 'orange']  # can support 3 unary relation and 8 binary relations
# a fixed colour scheme is used for predictability of state of a node

def getGraph(unv, interp):
	global nshape, node_color
	# ax = plot.gca()
	# ax.collections[0].set_edgecolor("#000000")
	i = 0 
	g = nx.MultiGraph()
	for sort in unv.keys():  # adding nodes
		attr = {'sort': sort, 'shape' : nshape[i], 'cnum' : 0} # cnum is color number, <TODO> use colormap to support more than 3 unary relation
		for const in unv[sort]:
			g.add_node(str(const), sort=sort, shape=nshape[i], cnum=0)
		i+=1

	unary_relOrder = {}
	bin_relOrder = {}
	for key, value in interp.valof.iteritems(): # adding edges and colouring nodes
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
				if value.val=='1':
					g.nodes[nodes[0]]['cnum'] = g.nodes[nodes[0]]['cnum'] +2**num/8.0
				if g.nodes[nodes[0]]['cnum'] > 1:  # for cmap to work, values of color should be between 0 to 1
					a = int(g.nodes[nodes[0]]['cnum']*8)%8
					g.nodes[nodes[0]]['cnum'] = a/8.0
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
				attr = {'color' : node_color[num+1], 'rel_name' : name, 'cnum' : (num%8)/8.0}
				g.add_edges_from([(nodes[0], nodes[1], attr)])
	
	for node in g.nodes():
		cnum = int(g.nodes[node]['cnum']*8)
		assert cnum==g.nodes[node]['cnum']*8, ""
		g.nodes[node]['color'] = node_color[cnum]

	return g


def displayStates(slabel, graph0, graph1=None):
	fig, ax = plot.subplots(nrows=1, ncols=2,figsize=(10, 5))
	fig.suptitle('{} sample'.format('Positve' if slabel=='1' else 'Negative'))
	if graph1!=None:
		plot.subplot(121)
	else:
		plot.subplot(111)
	plot.title("prestate")
	plotGraph(graph0)
	# plot.axis('off')
	if graph1!=None:	
		plot.subplot(122)
		plot.title("poststate")
		plotGraph(graph1)
	# plot.axis('off')
	plot.show()

def plotGraph(graph):
	'''
	assume graph is multigraph, each node has attribute cnum and shape, each node has attr cnum
	'''
	global nshape
	node_cmap = plot.get_cmap('Set3') # set of 12 colors
	edge_cmap = plot.get_cmap('Dark2') # cmap coressponds to color map
	pos = nx.circular_layout(graph, scale=.10)
	for shape in nshape:
		nodelist = []
		ncolor = []
		for node in graph.nodes():
			# print graph.nodes[node]
			if graph.nodes[node]['shape']==shape:
				nodelist.append(node)
				ncolor.append(graph.nodes[node]['cnum'])
		if len(nodelist)==0: # shapes are assigned sequentially 
			break
		npos = nx.circular_layout(nodelist, scale=.10)
		nx.draw_networkx_nodes(graph, pos, node_size=750, nodelist=nodelist, node_color=ncolor, cmap=node_cmap, vmin=0.0, vmax=1.0, node_shape=shape)
	ecolor = []
	for e in graph.edges(keys=True):
		ecolor.append(graph.edges[e[0],e[1],e[2]]['cnum'])
	nx.draw_networkx_edges(graph, pos, edge_color=ecolor ,edge_cmap=edge_cmap, edge_vmin=0.0, edge_vmax=1.0)
	nx.draw_networkx_labels(graph, pos=pos)


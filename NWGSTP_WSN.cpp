// NWGSTP_WSN.cpp : Defines the entry point for the console application.

#include "stdafx.h"
#include <iostream>
#include <fstream>
#include <boost/numeric/ublas/vector.hpp>
#include <boost/numeric/ublas/vector_proxy.hpp>
#include <boost/graph/adjacency_list.hpp>
#include <ctime>
#include <cstdlib>
#include <chrono>
#include <boost/graph/connected_components.hpp>
#include <boost/numeric/ublas/matrix.hpp>
#include <boost/numeric/ublas/matrix_proxy.hpp>
#include <boost/numeric/ublas/lu.hpp>
#include <boost/numeric/ublas/io.hpp>
#include <boost/heap/pairing_heap.hpp> // pairing_heap uses less memory
#include <boost/graph/prim_minimum_spanning_tree.hpp>
using namespace boost::heap;
using namespace boost::numeric::ublas; // there is a vector file inside which conflicts with std; so use std::vector to specify the vector definition
using namespace std;


#pragma region 
// define an adjacency list with edge weights
typedef boost::property<boost::edge_weight_t, double> EdgeWeightProperty; // define edge weight property
typedef boost::property<boost::vertex_name_t, double> VertexWeightProperty; // define node weight property; note that: vertex_index_t is not mutable
typedef boost::adjacency_list<boost::setS, boost::vecS,
	boost::undirectedS, VertexWeightProperty, EdgeWeightProperty> graph; // define all the graph properties
typedef boost::graph_traits<graph>::adjacency_iterator AdjacencyIterator;
#pragma endregion define graph property 2018年1月6日16:31:58


#pragma region
struct node_max_heap {
	int index;
	double priority_value;
}; // define the node in the queue
bool operator<(node_max_heap const& x, node_max_heap const& y) {
	return x.priority_value < y.priority_value; // < is the max-heap; > is the mean heap; PriorityQueue is expected to be a max-heap of integer values
} // redefine the operator since there are multiple values in each node
typedef typename pairing_heap<node_max_heap>::handle_type handle_t_node_max_heap; // define the handle type for pairing_heap<node>
#pragma endregion define max heaps 


#pragma region
struct node_min_heap {
	int index;
	double priority_value;
}; // define the node in the queue
bool operator<(node_min_heap const& x, node_min_heap const& y) {
	return x.priority_value > y.priority_value; // < is the max-heap; > is the mean heap; PriorityQueue is expected to be a max-heap of integer values
} // redefine the operator since there are multiple values in each node
typedef typename pairing_heap<node_min_heap>::handle_type handle_t_node_min_heap; // define the handle type for pairing_heap<node>
#pragma endregion define heaps 2018年1月20日17:3:52


#pragma region 
bool solution_contain_all_groups(int N, std::vector<int> included_vertices, graph group_graph) {

	int N_group = num_vertices(group_graph) - N;

	std::vector<bool> group_check(N_group);
	typedef boost::graph_traits<graph>::adjacency_iterator AdjacencyIterator;
	AdjacencyIterator ai, a_end;

	for (int i = 0; i < included_vertices.size(); i++) {
		boost::tie(ai, a_end) = boost::adjacent_vertices(included_vertices[i], group_graph); // groups of included_vertices[i]
		for (; ai != a_end; ai++) {
			int j = *ai; // group j-N
			group_check[j - N] = true; // group j-N is in solution
		}
	}

	for (int i = 0; i < N_group; i++) {
		if (group_check[i] == false) {
			return false;
		}
	}
	return true;

}
#pragma endregion solution_contain_all_groups  2018年4月28日16:43:07


#pragma region

double net_cost(graph input_graph, std::vector<int> included_vertices) {

	// included edge costs minus included node weights

	typedef boost::graph_traits<graph>::adjacency_iterator AdjacencyIterator;
	AdjacencyIterator ai, a_end;

	double included_cost = 0;
	for (int i = 0; i < included_vertices.size(); i++) {
		included_cost = included_cost - get(boost::vertex_name_t(), input_graph, included_vertices[i]); // minus included node weights
		boost::tie(ai, a_end) = boost::adjacent_vertices(included_vertices[i], input_graph); // we assume *ai is also in the solution
		for (; ai != a_end; ai++) {
			if (*ai < included_vertices[i]) {
				included_cost = included_cost +
					get(boost::edge_weight_t(), input_graph, boost::edge(included_vertices[i], *ai, input_graph).first); // included edge costs
			}
		}
	}

	return included_cost;


}

#pragma endregion net_cost  2018年1月15日10:20:29


#pragma region
graph copy_graph(graph input_graph) {

	graph output_graph = input_graph; // this input_graph is just a copy of the outside input_graph

	return output_graph;

}
#pragma endregion copy_graph 2017年11月22日13:05:11


#pragma region
std::vector<int> copy_vector_int(std::vector<int> input_vector) {

	std::vector<int> output_vector = input_vector;

	return output_vector;

}
#pragma endregion copy_vector_int 2018年2月10日13:25:57


#pragma region
std::vector<string> copy_vector_string(std::vector<string> input_vector) {

	std::vector<string> output_vector = input_vector;

	return output_vector;

}
#pragma endregion copy_vector_string


#pragma region
void connectivity_check_ignore_isolated_vertices(int N, graph RT_graph) {
	std::vector<int> component(N); // vertex i is in component[i]; No.component from 0
	int cpn_num = connected_components(RT_graph, &component[0]); // the number of component; decrease component
	int cpn_target;
	for (int i = 0; i < N; i++) {
		if (in_degree(i, RT_graph) > 0) {
			cpn_target = component[i];
			break;
		}
	}
	for (int i = 0; i < N; i++) {
		if (in_degree(i, RT_graph) > 0 && component[i] != cpn_target) {
			cout << "SMT is disconnected" << endl;
			getchar();
			break;
		}
	}
}
#pragma endregion  connectivity_check_ignore_isolated_vertices  2018年1月17日23:00:16


#pragma region

bool compare1(int i, int j)
{
	return i < j;  // < is from sort small to big; > is from big to small
}


std::vector<int> find_included_vertices(graph input_graph, graph group_graph, graph solution_graph) {

	int N = num_vertices(solution_graph);
	int N_group = num_vertices(group_graph) - N;

	std::vector<int> included_vertices;

	if (num_edges(solution_graph) > 0) { // we assume that all edges are connected with each other 

		for (int i = 0; i < N; i++) {
			if (in_degree(i, solution_graph) > 0) {
				included_vertices.insert(included_vertices.end(), i); // from small to large number
			}
		}

	}
	else { // the solution is a single vertex; we assume that there is a feasible solution

		double max_nw = -1e8;
		int solution_vertex;
		for (int i = 0; i < N; i++) {
			if (in_degree(i, group_graph) == N_group) { // this vertex is contained by every group, and thus is a feasible solution
				double i_nw = get(boost::vertex_name_t(), input_graph, i);
				if (i_nw > max_nw) {
					max_nw = i_nw;
					solution_vertex = i;
				}
			}
		}
		included_vertices.insert(included_vertices.end(), solution_vertex); // solution_vertex is the feasible solution with the largest nw

	}

	return included_vertices;

}


void insert_included_vertices(std::vector<int>& included_vertices, std::vector<int> inserted_vertices) {

	// you can also sort inserted_vertices, and insert them one by one, but you need many if, it may be slower than sort new included_vertices

	for (int i = 0; i < inserted_vertices.size(); i++) {
		included_vertices.insert(included_vertices.end(), inserted_vertices[i]);
	}
	sort(included_vertices.begin(), included_vertices.end(), compare1);

}


void remove_included_vertices(std::vector<int>& included_vertices, std::vector<int> removed_vertices) {

	// we assume all elements in removed_vertices are also in included_vertices

	if (removed_vertices.size() > 1) {

		sort(removed_vertices.begin(), removed_vertices.end(), compare1);
		for (int i = 0; i < included_vertices.size(); i++) {
			if (included_vertices[i] == removed_vertices[0]) {
				included_vertices.erase(included_vertices.begin() + i);
				removed_vertices.erase(removed_vertices.begin());
				if (removed_vertices.size() == 0) {
					break;
				}
				i--;
			}
		}

	}
	else if (removed_vertices.size() == 1) {

		for (int i = 0; i < included_vertices.size(); i++) {
			if (included_vertices[i] == removed_vertices[0]) {
				included_vertices.erase(included_vertices.begin() + i);
				break;
			}
		}

	}

}


#pragma endregion find_included_vertices   insert_included_vertices   remove_included_vertices  2018年4月28日16:44:58


#pragma region
void save_NWGSTP_graph(string instance_name, graph result_graph, graph group_graph) {

	string save_name = instance_name; // save_name
	ofstream outputFile;
	outputFile.precision(4);
	outputFile.setf(ios::fixed);
	outputFile.setf(ios::showpoint);
	outputFile.open(save_name + ".stp"); // stp file

	outputFile << "33D32945 STP File, STP Format Version 1.0" << endl;
	outputFile << endl;

	// comments
	outputFile << "SECTION Comments" << endl;
	outputFile << "Name \"" << save_name << "\"" << endl;
	outputFile << "Creator \"Yahui Sun\"" << endl;
	outputFile << "Problem \"Node - Weighted Partial Full Group Steiner Problem in Graphs\"" << endl;
	outputFile << "END" << endl;
	outputFile << endl;

	// graph
	outputFile << "SECTION Graph" << endl;
	outputFile << "Nodes " << num_vertices(result_graph) << endl;
	outputFile << "Edges " << num_edges(result_graph) << endl;
	graph::out_edge_iterator eit, eend;
	for (int i = 0; i < num_vertices(result_graph); i++) {
		tie(eit, eend) = boost::out_edges(i, result_graph); // adjacent_vertices of 2
		for_each(eit, eend,
			[&result_graph, &i, &outputFile](graph::edge_descriptor it)
		{
			int j = boost::target(it, result_graph);
			if (i < j) {
				outputFile << "E " << i + 1 << " " << j + 1 << " " << get(boost::edge_weight_t(), result_graph, boost::edge(i, j, result_graph).first) << endl;
			}
		});
	}
	outputFile << "END" << endl;
	outputFile << endl;

	// TP
	outputFile << "SECTION Node Weights" << endl;
	for (int i = 0; i < num_vertices(result_graph); i++) {
		outputFile << "TP " << i + 1 << " " << get(boost::vertex_name_t(), result_graph, i) << endl;
	}
	outputFile << "END" << endl;
	outputFile << endl;

	// Group
	outputFile << "SECTION Group Vertices" << endl;
	int N = num_vertices(result_graph);
	int N_group = num_vertices(group_graph) - N;
	typedef boost::graph_traits<graph>::adjacency_iterator AdjacencyIterator;
	AdjacencyIterator ai, a_end;
	for (int i = 0; i < N_group; i++) {
		outputFile << "G";
		boost::tie(ai, a_end) = boost::adjacent_vertices(i + N, group_graph);
		for (; ai != a_end; ai++) {
			int j = *ai;
			outputFile << " " << j + 1;
		}
		outputFile << endl;
	}
	outputFile << "END" << endl;
	outputFile << endl;


	outputFile << "EOF" << endl;

}
#pragma endregion save_NWGSTP_graph 


#pragma region
void save_NWFGSTP_graph(string instance_name, graph result_graph, graph group_graph, std::vector<int> LV) {

	string save_name = instance_name; // save_name
	ofstream outputFile;
	outputFile.precision(4);
	outputFile.setf(ios::fixed);
	outputFile.setf(ios::showpoint);
	outputFile.open(save_name + ".stp"); // stp file

	outputFile << "33D32945 STP File, STP Format Version 1.0" << endl;
	outputFile << endl;

	// comments
	outputFile << "SECTION Comments" << endl;
	outputFile << "Name \"" << save_name << "\"" << endl;
	outputFile << "Creator \"Yahui Sun\"" << endl;
	outputFile << "Problem \"Node - Weighted Partial Full Group Steiner Problem in Graphs\"" << endl;
	outputFile << "END" << endl;
	outputFile << endl;

	// graph
	outputFile << "SECTION Graph" << endl;
	outputFile << "Nodes " << num_vertices(result_graph) << endl;
	outputFile << "Edges " << num_edges(result_graph) << endl;
	graph::out_edge_iterator eit, eend;
	for (int i = 0; i < num_vertices(result_graph); i++) {
		tie(eit, eend) = boost::out_edges(i, result_graph); // adjacent_vertices of 2
		for_each(eit, eend,
			[&result_graph, &i, &outputFile](graph::edge_descriptor it)
		{
			int j = boost::target(it, result_graph);
			if (i < j) {
				outputFile << "E " << i + 1 << " " << j + 1 << " " << get(boost::edge_weight_t(), result_graph, boost::edge(i, j, result_graph).first) << endl;
			}
		});
	}
	outputFile << "END" << endl;
	outputFile << endl;

	// TP
	outputFile << "SECTION Node Weights" << endl;
	for (int i = 0; i < num_vertices(result_graph); i++) {
		outputFile << "TP " << i + 1 << " " << get(boost::vertex_name_t(), result_graph, i) << endl;
	}
	outputFile << "END" << endl;
	outputFile << endl;

	// Group
	outputFile << "SECTION Group Vertices" << endl;
	int N = num_vertices(result_graph);
	int N_group = num_vertices(group_graph) - N;
	typedef boost::graph_traits<graph>::adjacency_iterator AdjacencyIterator;
	AdjacencyIterator ai, a_end;
	for (int i = 0; i < N_group; i++) {
		outputFile << "G";
		boost::tie(ai, a_end) = boost::adjacent_vertices(i + N, group_graph);
		for (; ai != a_end; ai++) {
			int j = *ai;
			outputFile << " " << j + 1;
		}
		outputFile << endl;
	}
	outputFile << "END" << endl;
	outputFile << endl;


	// LV
	outputFile << "SECTION Leaf Vertices" << endl;
	for (int i = 0; i < N; i++) {
		if (LV[i] == 1) {
			outputFile << "LV " << i + 1 << endl;
		}
	}
	outputFile << "END" << endl;
	outputFile << endl;


	outputFile << "EOF" << endl;

}
#pragma endregion save_NWFGSTP_graph 


#pragma region  
graph read_NWGSTP_data(string file_name, graph& group_graph) {

	group_graph.clear(); // 

	int V_num; // vertex number
	int P_num; // number of positive vertices
	int E_num; // edge number
	int v1;
	int v2;
	double weight;
	int group_id = 0;
	graph input_graph; // define the adjacency list of the input graph; there is no need to define the V_num
	string line_content;
	ifstream myfile(file_name); // open the file
	if (myfile.is_open()) // if the file is opened successfully
	{
		while (getline(myfile, line_content)) // read file line by line
		{
			// parse the sting：line_content
			list<string> Parsed_content;
			std::string delimiter = " "; // the delimiter
			size_t pos = 0;
			std::string token;
			while ((pos = line_content.find(delimiter)) != std::string::npos) {
				// find(const string& str, size_t pos = 0) function returns the position of the first occurrence of str in the string, or npos if the string is not found.
				token = line_content.substr(0, pos);
				// The substr(size_t pos = 0, size_t n = npos) function returns a substring of the object, starting at position pos and of length npos
				Parsed_content.push_back(token); // store the subtr to the list
				line_content.erase(0, pos + delimiter.length()); // remove the front substr and the first delimiter
			}
			Parsed_content.push_back(line_content); // store the subtr to the list
			if (!Parsed_content.front().compare("Nodes")) // when it's equal, compare returns 0
			{
				Parsed_content.pop_front();
				V_num = atoi(Parsed_content.front().c_str()); // convert string to int
				for (int i = 0; i < V_num; i++) {
					boost::add_vertex(i, input_graph);
					boost::put(boost::vertex_name_t(), input_graph, i, 0);
				}
			}
			else if (!Parsed_content.front().compare("Edges"))
			{
				Parsed_content.pop_front();
				E_num = atoi(Parsed_content.front().c_str());
			}
			else if (!Parsed_content.front().compare("E"))
			{
				Parsed_content.pop_front(); // remove E, expose v1
				v1 = atoi(Parsed_content.front().c_str()) - 1;
				Parsed_content.pop_front(); // remove v1, expose v2
				v2 = atoi(Parsed_content.front().c_str()) - 1;
				Parsed_content.pop_front(); // remove v2, expose weight
				weight = stof(Parsed_content.front().c_str());
				boost::add_edge(v1, v2, weight, input_graph); // add edge
			}
			else if (!Parsed_content.front().compare("TP"))
			{
				Parsed_content.pop_front(); // remove TP, expose v1
				v1 = atoi(Parsed_content.front().c_str()) - 1;
				Parsed_content.pop_front(); // remove v1, expose weight
				boost::put(boost::vertex_name_t(), input_graph, v1, stof(Parsed_content.front().c_str()));
			}
			else if (!Parsed_content.front().compare("G"))
			{
				boost::add_vertex(group_id + V_num, group_graph);
				Parsed_content.pop_front(); // remove G, expose v1

				while (Parsed_content.size() > 0) {
					v1 = atoi(Parsed_content.front().c_str()) - 1;
					boost::add_edge(group_id + V_num, v1, 1, group_graph);
					Parsed_content.pop_front();
				}

				group_id++;
			}
		}

		// check number of vertices
		std::cout << "|V|= " << num_vertices(input_graph);
		//std::cout << "  |P|= " << P_num;
		// check number of edges
		std::cout << "  |E|= " << num_edges(input_graph);
		// print errors
		if (V_num != num_vertices(input_graph)) {
			std::cout << "Error: the number of the input vertices is not right." << endl;
		}
		if (E_num != num_edges(input_graph)) {
			std::cout << "Error: the number of the input edges is not right." << endl;
		}
		return input_graph;

		myfile.close(); //close the file
	}
	else
	{
		std::cout << "Unable to open file " << file_name << endl << "Please check the file location or file name." << endl; // throw an error message
		getchar(); // keep the console window
		exit(1); // end the program
	}
}
#pragma endregion read_NWGSTP_data


#pragma region  
graph read_NWFGSTP_data(string file_name, graph& group_graph, std::vector<int>& LV) {

	group_graph.clear(); // 
	LV.clear();

	int V_num; // vertex number
	int P_num; // number of positive vertices
	int E_num; // edge number
	int v1;
	int v2;
	double weight;
	int group_id = 0;
	graph input_graph; // define the adjacency list of the input graph; there is no need to define the V_num
	string line_content;
	ifstream myfile(file_name); // open the file
	if (myfile.is_open()) // if the file is opened successfully
	{
		while (getline(myfile, line_content)) // read file line by line
		{
			// parse the sting：line_content
			list<string> Parsed_content;
			std::string delimiter = " "; // the delimiter
			size_t pos = 0;
			std::string token;
			while ((pos = line_content.find(delimiter)) != std::string::npos) {
				// find(const string& str, size_t pos = 0) function returns the position of the first occurrence of str in the string, or npos if the string is not found.
				token = line_content.substr(0, pos);
				// The substr(size_t pos = 0, size_t n = npos) function returns a substring of the object, starting at position pos and of length npos
				Parsed_content.push_back(token); // store the subtr to the list
				line_content.erase(0, pos + delimiter.length()); // remove the front substr and the first delimiter
			}
			Parsed_content.push_back(line_content); // store the subtr to the list
			if (!Parsed_content.front().compare("Nodes")) // when it's equal, compare returns 0
			{
				Parsed_content.pop_front();
				V_num = atoi(Parsed_content.front().c_str()); // convert string to int
				for (int i = 0; i < V_num; i++) {
					boost::add_vertex(i, input_graph);
					boost::put(boost::vertex_name_t(), input_graph, i, 0);
				}
				LV.resize(V_num);
			}
			else if (!Parsed_content.front().compare("Edges"))
			{
				Parsed_content.pop_front();
				E_num = atoi(Parsed_content.front().c_str());
			}
			else if (!Parsed_content.front().compare("E"))
			{
				Parsed_content.pop_front(); // remove E, expose v1
				v1 = atoi(Parsed_content.front().c_str()) - 1;
				Parsed_content.pop_front(); // remove v1, expose v2
				v2 = atoi(Parsed_content.front().c_str()) - 1;
				Parsed_content.pop_front(); // remove v2, expose weight
				weight = stof(Parsed_content.front().c_str());
				boost::add_edge(v1, v2, weight, input_graph); // add edge
			}
			else if (!Parsed_content.front().compare("TP"))
			{
				Parsed_content.pop_front(); // remove TP, expose v1
				v1 = atoi(Parsed_content.front().c_str()) - 1;
				Parsed_content.pop_front(); // remove v1, expose weight
				boost::put(boost::vertex_name_t(), input_graph, v1, stof(Parsed_content.front().c_str()));
			}
			else if (!Parsed_content.front().compare("G"))
			{
				boost::add_vertex(group_id + V_num, group_graph);
				Parsed_content.pop_front(); // remove G, expose v1

				while (Parsed_content.size() > 0) {
					v1 = atoi(Parsed_content.front().c_str()) - 1;
					boost::add_edge(group_id + V_num, v1, 1, group_graph);
					Parsed_content.pop_front();
				}

				group_id++;
			}
			else if (!Parsed_content.front().compare("LV"))
			{
				Parsed_content.pop_front(); // remove LV, expose v1+1
				v1 = atoi(Parsed_content.front().c_str()) - 1;
				LV[v1] = 1;
			}
		}

		// check number of vertices
		std::cout << "|V|= " << num_vertices(input_graph);
		//std::cout << "  |P|= " << P_num;
		// check number of edges
		std::cout << "  |E|= " << num_edges(input_graph);
		// print errors
		if (V_num != num_vertices(input_graph)) {
			std::cout << "Error: the number of the input vertices is not right." << endl;
		}
		if (E_num != num_edges(input_graph)) {
			std::cout << "Error: the number of the input edges is not right." << endl;
		}
		return input_graph;

		myfile.close(); //close the file
	}
	else
	{
		std::cout << "Unable to open file " << file_name << endl << "Please check the file location or file name." << endl; // throw an error message
		getchar(); // keep the console window
		exit(1); // end the program
	}
}
#pragma endregion read_NWFGSTP_data


#pragma region
graph leaf_replacing(graph input_graph, graph group_graph, graph solution_graph, std::vector<int>& included_vertices) {

	if (num_edges(solution_graph) == 0) { // return solution_graph when it's empty
		return solution_graph;
	}

	int N = num_vertices(input_graph);

	typedef boost::graph_traits<graph>::adjacency_iterator AdjacencyIterator;
	AdjacencyIterator ai, a_end;
	AdjacencyIterator bi, b_end;

	std::vector<int> solution_graph_leaves;
	std::vector<int> potential_new_leaf_check(N);
	std::vector<int> potential_new_leaf; // outside vertices share groups with existing leaves
	for (int i = 0; i < included_vertices.size(); i++) {
		if (in_degree(included_vertices[i], solution_graph) == 1) { // an existing leaf
			solution_graph_leaves.insert(solution_graph_leaves.end(), included_vertices[i]); // solution_graph_leaves contains all leaves
			boost::tie(ai, a_end) = boost::adjacent_vertices(included_vertices[i], group_graph);
			for (; ai != a_end; ai++) {
				int j = *ai; // the existing leaf is in group j-N
				boost::tie(bi, b_end) = boost::adjacent_vertices(j, group_graph);
				for (; bi != b_end; bi++) {
					int k = *bi; // vertex k shares this group with the existing leaf
					if (potential_new_leaf_check[k] == 0 && in_degree(k, solution_graph) == 0) { // outside vertices
						potential_new_leaf.insert(potential_new_leaf.end(), k);
					}
					potential_new_leaf_check[k] = 1;
				}
			}

		}
	}

	//cout << "a " << potential_new_leaf.size() << endl;

	for (int i = 0; i < potential_new_leaf.size(); i++) {

		double saved_cost = 0;
		int new_edge_j;
		std::vector<int> removed_leaves;

		boost::tie(ai, a_end) = boost::adjacent_vertices(potential_new_leaf[i], input_graph);

		for (; ai != a_end; ai++) { // don't use new ai aa_end in this loop
			int j = *ai;
			if (in_degree(j, solution_graph) > 0) {//potential_new_leaf[i] is adjacent to solution; (potential_new_leaf[i],j) is a possible new edge
				// add (potential_new_leaf[i],j) to solution, remove other leaves; find save-cost for (potential_new_leaf[i],j)

				//cout << "check " << j << endl;
				std::vector<int> potential_removed_leaves;
				double saved_cost_j = 0;
				std::vector<int> new_included_vertices = copy_vector_int(included_vertices); // copy included_vertices
				insert_included_vertices(new_included_vertices, { potential_new_leaf[i] }); // add new leaf

				for (int k = 0; k < solution_graph_leaves.size(); k++) { // check old group leaf
					if (solution_graph_leaves[k] != j && in_degree(solution_graph_leaves[k], group_graph) > 0) { // old group leaf is not j
						remove_included_vertices(new_included_vertices, { solution_graph_leaves[k] }); // remove this old group leaf
						if (solution_contain_all_groups(N, new_included_vertices, group_graph) == true) { // feasible without this old leaf and previous potential_removed_leaves
							potential_removed_leaves.insert(potential_removed_leaves.end(), solution_graph_leaves[k]);
							boost::tie(bi, b_end) = boost::adjacent_vertices(solution_graph_leaves[k], solution_graph);
							saved_cost_j = saved_cost_j +
								get(boost::edge_weight_t(), input_graph, boost::edge(*bi, solution_graph_leaves[k], input_graph).first)
								- get(boost::vertex_name_t(), input_graph, solution_graph_leaves[k]); // removed cost
							//cout << *bi << "," << solution_graph_leaves[k] <<" saved_cost_j " << saved_cost_j << endl;
						}
						else { // infeasible, return this old group leaf
							insert_included_vertices(new_included_vertices, { solution_graph_leaves[k] });
						}
					}
				}
				saved_cost_j = saved_cost_j + get(boost::vertex_name_t(), input_graph, potential_new_leaf[i]) -
					get(boost::edge_weight_t(), input_graph, boost::edge(potential_new_leaf[i], j, input_graph).first); // - added cost
				//cout << "saved_cost_j " << saved_cost_j << endl;

				if (saved_cost_j > saved_cost) {
					saved_cost = saved_cost_j;
					new_edge_j = j;
					removed_leaves = copy_vector_int(potential_removed_leaves);
				}
			}
		}

		if (saved_cost > 0) {
			boost::add_edge(potential_new_leaf[i], new_edge_j, get(boost::edge_weight_t(), input_graph,
				boost::edge(potential_new_leaf[i], new_edge_j, input_graph).first), solution_graph); // add edge to solution_graph
			if (in_degree(new_edge_j, solution_graph) == 2) { // new_edge_j was previously a leaf
				remove_included_vertices(solution_graph_leaves, { new_edge_j }); // remove this old leaf
			}
			insert_included_vertices(solution_graph_leaves, { potential_new_leaf[i] }); // insert this new leaf
			//cout << "LRA add " << potential_new_leaf[i] << "," << new_edge_j << endl;
			//cout << "saved_cost " << saved_cost << endl;
			insert_included_vertices(included_vertices, { potential_new_leaf[i] }); // update included_vertices
			for (int k = 0; k < removed_leaves.size(); k++) {
				//cout << "LRA Clear " << removed_leaves[k] << endl;
				boost::tie(ai, a_end) = boost::adjacent_vertices(removed_leaves[k], solution_graph);
				int adj = *ai;
				boost::remove_edge(removed_leaves[k], adj, solution_graph); // remove edges from solution_graph
				remove_included_vertices(solution_graph_leaves, { removed_leaves[k] }); // remove this old leaf
				if (in_degree(adj, solution_graph) == 1) { // adj is a new leaf
					insert_included_vertices(solution_graph_leaves, { adj }); // insert this new leaf
				}
				remove_included_vertices(included_vertices, { removed_leaves[k] }); // update included_vertices
				potential_new_leaf.insert(potential_new_leaf.end(), removed_leaves[k]); // mark the removed leaf as a new potential_new_leaf
				//getchar();
			}
		}

	}

	//for (int i = 0; i < potential_new_leaf.size(); i++) {
	//	cout << "potential_new_leaf " << potential_new_leaf[i] << endl;
	//}

	return solution_graph;

}
#pragma endregion leaf_replacing


#pragma region
graph leaf_replacing_NWFGSTP(graph input_graph, graph group_graph, graph solution_graph, std::vector<int>& included_vertices, std::vector<int> LV) {

	if (num_edges(solution_graph) == 0) { // return solution_graph when it's empty
		return solution_graph;
	}

	int N = num_vertices(input_graph);

	typedef boost::graph_traits<graph>::adjacency_iterator AdjacencyIterator;
	AdjacencyIterator ai, a_end;
	AdjacencyIterator bi, b_end;

	std::vector<int> solution_graph_leaves;
	std::vector<int> potential_new_leaf_check(N);
	std::vector<int> potential_new_leaf; // outside vertices share groups with existing leaves
	for (int i = 0; i < included_vertices.size(); i++) {
		if (in_degree(included_vertices[i], solution_graph) == 1) { // an existing leaf
			solution_graph_leaves.insert(solution_graph_leaves.end(), included_vertices[i]); // solution_graph_leaves contains all leaves
			boost::tie(ai, a_end) = boost::adjacent_vertices(included_vertices[i], group_graph);
			for (; ai != a_end; ai++) {
				int j = *ai; // the existing leaf is in group j-N
				boost::tie(bi, b_end) = boost::adjacent_vertices(j, group_graph);
				for (; bi != b_end; bi++) {
					int k = *bi; // vertex k shares this group with the existing leaf
					if (potential_new_leaf_check[k] == 0 && in_degree(k, solution_graph) == 0) { // outside vertices
						potential_new_leaf.insert(potential_new_leaf.end(), k);
					}
					potential_new_leaf_check[k] = 1;
				}
			}

		}
	}

	//cout << "a " << potential_new_leaf.size() << endl;

	for (int i = 0; i < potential_new_leaf.size(); i++) {

		double saved_cost = 0;
		int new_edge_j;
		std::vector<int> removed_leaves;

		boost::tie(ai, a_end) = boost::adjacent_vertices(potential_new_leaf[i], input_graph);

		for (; ai != a_end; ai++) { // don't use new ai aa_end in this loop
			int j = *ai;
			if (in_degree(j, solution_graph) > 0 && LV[j] == 0) {//potential_new_leaf[i] is adjacent to solution; (potential_new_leaf[i],j) is a possible new edge
				// add (potential_new_leaf[i],j) to solution, remove other leaves; find save-cost for (potential_new_leaf[i],j)
				// (potential_new_leaf[i],j) won't turn leaf vertices as non-leaves

				//cout << "check " << j << endl;
				std::vector<int> potential_removed_leaves;
				double saved_cost_j = 0;
				std::vector<int> new_included_vertices = copy_vector_int(included_vertices); // copy included_vertices
				insert_included_vertices(new_included_vertices, { potential_new_leaf[i] }); // add new leaf

				for (int k = 0; k < solution_graph_leaves.size(); k++) { // check old group leaf
					if (solution_graph_leaves[k] != j && in_degree(solution_graph_leaves[k], group_graph) > 0) { // old group leaf is not j
						remove_included_vertices(new_included_vertices, { solution_graph_leaves[k] }); // remove this old group leaf
						if (solution_contain_all_groups(N, new_included_vertices, group_graph) == true) { // feasible without this old leaf and previous potential_removed_leaves
							potential_removed_leaves.insert(potential_removed_leaves.end(), solution_graph_leaves[k]);
							boost::tie(bi, b_end) = boost::adjacent_vertices(solution_graph_leaves[k], solution_graph);
							saved_cost_j = saved_cost_j +
								get(boost::edge_weight_t(), input_graph, boost::edge(*bi, solution_graph_leaves[k], input_graph).first)
								- get(boost::vertex_name_t(), input_graph, solution_graph_leaves[k]); // removed cost
																									  //cout << *bi << "," << solution_graph_leaves[k] <<" saved_cost_j " << saved_cost_j << endl;
						}
						else { // infeasible, return this old group leaf
							insert_included_vertices(new_included_vertices, { solution_graph_leaves[k] });
						}
					}
				}
				saved_cost_j = saved_cost_j + get(boost::vertex_name_t(), input_graph, potential_new_leaf[i]) -
					get(boost::edge_weight_t(), input_graph, boost::edge(potential_new_leaf[i], j, input_graph).first); // - added cost
																														//cout << "saved_cost_j " << saved_cost_j << endl;

				if (saved_cost_j > saved_cost) {
					saved_cost = saved_cost_j;
					new_edge_j = j;
					removed_leaves = copy_vector_int(potential_removed_leaves);
				}
			}
		}

		if (saved_cost > 0) {
			boost::add_edge(potential_new_leaf[i], new_edge_j, get(boost::edge_weight_t(), input_graph,
				boost::edge(potential_new_leaf[i], new_edge_j, input_graph).first), solution_graph); // add edge to solution_graph
			if (in_degree(new_edge_j, solution_graph) == 2) { // new_edge_j was previously a leaf
				remove_included_vertices(solution_graph_leaves, { new_edge_j }); // remove this old leaf
			}
			insert_included_vertices(solution_graph_leaves, { potential_new_leaf[i] }); // insert this new leaf
																						//cout << "LRA add " << potential_new_leaf[i] << "," << new_edge_j << endl;
																						//cout << "saved_cost " << saved_cost << endl;
			insert_included_vertices(included_vertices, { potential_new_leaf[i] }); // update included_vertices
			for (int k = 0; k < removed_leaves.size(); k++) {
				//cout << "LRA Clear " << removed_leaves[k] << endl;
				boost::tie(ai, a_end) = boost::adjacent_vertices(removed_leaves[k], solution_graph);
				int adj = *ai;
				boost::remove_edge(removed_leaves[k], adj, solution_graph); // remove edges from solution_graph
				remove_included_vertices(solution_graph_leaves, { removed_leaves[k] }); // remove this old leaf
				if (in_degree(adj, solution_graph) == 1) { // adj is a new leaf
					insert_included_vertices(solution_graph_leaves, { adj }); // insert this new leaf
				}
				remove_included_vertices(included_vertices, { removed_leaves[k] }); // update included_vertices
				potential_new_leaf.insert(potential_new_leaf.end(), removed_leaves[k]); // mark the removed leaf as a new potential_new_leaf
																						//getchar();
			}
		}

	}

	//for (int i = 0; i < potential_new_leaf.size(); i++) {
	//	cout << "potential_new_leaf " << potential_new_leaf[i] << endl;
	//}

	return solution_graph;

}
#pragma endregion leaf_replacing_NWFGSTP


#pragma region
graph branch_replacing(graph input_graph, graph group_graph, graph solution_graph, std::vector<int>& included_vertices, int alpha) {

	if (num_edges(solution_graph) == 0) { // return solution_graph when it's empty
		return solution_graph;
	}

	int N = num_vertices(input_graph);

	typedef boost::graph_traits<graph>::adjacency_iterator AdjacencyIterator;
	AdjacencyIterator ai, a_end;
	AdjacencyIterator bi, b_end;
	typedef graph::edge_descriptor Edge;
	//srand(time(NULL)); //  seed random number generator

	// randomly select a inside group vertex as the root
	int N_group = num_vertices(group_graph) - N;
	int RAND = rand() % N_group; // random number 0,N_group-1; it's much slower to generate random vertex and then check it's in group or not
	boost::tie(ai, a_end) = boost::adjacent_vertices(N + RAND, group_graph);
	//cout << num_vertices(group_graph) << endl;
	//cout << N << endl;
	//cout << N_group << endl;
	//cout << RAND << endl;
	int root;
	for (; ai != a_end; ai++) {
		if (in_degree(*ai, solution_graph) > 0) {
			root = *ai;  // the first inside vertex in this random group is the root
			break;
		}
	}

	//cout << "root " << root << endl;

	std::vector<bool> tagged(N);
	std::vector<int> tagged_value(N); // corresponding to alpha
	std::vector<int> branch_begin(N);
	std::vector<int> predecessor(N);
	std::vector<int> to_be_tagged;

	tagged[root] = true; // tag root
	tagged_value[root] = 0;
	branch_begin[root] = root;
	boost::tie(ai, a_end) = boost::adjacent_vertices(root, solution_graph);
	for (; ai != a_end; ai++) {
		predecessor[*ai] = root; // every vertex in to_be_tagged has a predecessor
		to_be_tagged.insert(to_be_tagged.end(), *ai); // all adjacent vertices of root are to be tagged
	}
	for (int i = 0; i < to_be_tagged.size(); i++) { // all vertices in the solution will be tagged eventually

		//cout << "tagging " << to_be_tagged[i] << endl;
		if (in_degree(to_be_tagged[i], solution_graph) > 2 || in_degree(to_be_tagged[i], group_graph) > 0) { // to_be_tagged[i] is a junction or group vertex

			if (tagged_value[predecessor[to_be_tagged[i]]] >= alpha) { // a potential branch to_be_tagged[i],branch_begin[predecessor[to_be_tagged[i]]]

				// calculate branch_cost
				double branch_cost = 0;
				int v1 = to_be_tagged[i];
				int v2 = predecessor[to_be_tagged[i]];
				while (0 < 1) {
					branch_cost = branch_cost + get(boost::edge_weight_t(), input_graph, boost::edge(v1, v2, input_graph).first);
					if (v2 != branch_begin[v2]) {
						branch_cost = branch_cost - get(boost::vertex_name_t(), input_graph, v2); // v2 is in this branch
						v1 = v2;
						v2 = predecessor[v2];
					}
					else { // v2 is branch end
						break;
					}
				}

				// check component
				std::vector<int> component_m, component_n; // component_m is the root component (with v2 inside)
				boost::remove_edge(to_be_tagged[i], predecessor[to_be_tagged[i]], solution_graph); // component_n is isolated
				boost::remove_edge(v1, v2, solution_graph); // v2 = branch_begin[predecessor[to_be_tagged[i]]]; component_m is isolated
				std::vector<int> checked(N);
				std::vector<int> to_be_checked;
				component_m.insert(component_m.end(), v2); // v2 is in component_m
				checked[v2] = 1;
				boost::tie(ai, a_end) = boost::adjacent_vertices(v2, solution_graph);
				for (; ai != a_end; ai++) {
					component_m.insert(component_m.end(), *ai);
					to_be_checked.insert(to_be_checked.end(), *ai);
				}
				for (int j = 0; j < to_be_checked.size(); j++) {
					checked[to_be_checked[j]] = 1;
					boost::tie(ai, a_end) = boost::adjacent_vertices(to_be_checked[j], solution_graph);
					for (; ai != a_end; ai++) {
						if (checked[*ai] == 0) {
							component_m.insert(component_m.end(), *ai);
							to_be_checked.insert(to_be_checked.end(), *ai);
						}
					}
				}
				checked.clear();
				checked.resize(N);
				to_be_checked.clear();
				component_n.insert(component_n.end(), to_be_tagged[i]); // to_be_tagged[i] is in component_n
				checked[to_be_tagged[i]] = 1;
				boost::tie(ai, a_end) = boost::adjacent_vertices(to_be_tagged[i], solution_graph);
				for (; ai != a_end; ai++) {
					component_n.insert(component_n.end(), *ai);
					to_be_checked.insert(to_be_checked.end(), *ai);
				}
				for (int j = 0; j < to_be_checked.size(); j++) {
					checked[to_be_checked[j]] = 1;
					boost::tie(ai, a_end) = boost::adjacent_vertices(to_be_checked[j], solution_graph);
					for (; ai != a_end; ai++) {
						if (checked[*ai] == 0) {
							component_n.insert(component_n.end(), *ai);
							to_be_checked.insert(to_be_checked.end(), *ai);
						}
					}
				}
				// restore the two edges removed above
				boost::add_edge(to_be_tagged[i], predecessor[to_be_tagged[i]], get(boost::edge_weight_t(), input_graph,
					boost::edge(to_be_tagged[i], predecessor[to_be_tagged[i]], input_graph).first), solution_graph);
				boost::add_edge(v1, v2, get(boost::edge_weight_t(), input_graph, boost::edge(v1, v2, input_graph).first), solution_graph);

				// try to find the minimum-cost edge (m,n) to replace branch
				int m, n; // m in the root component, it may be untagged; n in the other compomnent, it must be untagged
				double c_mn = 1e9;
				for (int e1 = 0; e1 < component_m.size(); e1++) {
					for (int e2 = 0; e2 < component_n.size(); e2++) {
						pair<Edge, bool> ed = boost::edge(component_m[e1], component_n[e2], input_graph);
						if (ed.second) { // this edge exist
							double edge_cost =
								get(boost::edge_weight_t(), input_graph, boost::edge(component_m[e1], component_n[e2], input_graph).first);
							if (edge_cost < c_mn) {
								c_mn = edge_cost;
								m = component_m[e1];
								n = component_n[e2];
							}
						}
					}
				}


				if (c_mn < branch_cost) { // use (m,n) to replace branch

					//cout << "BRA add " << m << "," << n << ": " << c_mn << endl;

					// remove branch
					v1 = to_be_tagged[i];
					v2 = predecessor[to_be_tagged[i]];
					while (0 < 1) {
						boost::remove_edge(v1, v2, solution_graph);
						//cout << "BRA remove " << v1 << "," << v2 << endl;
						if (v2 != branch_begin[v2]) {
							remove_included_vertices(included_vertices, { v2 }); // remove inside vertices
							v1 = v2;
							v2 = predecessor[v2];
						}
						else {
							break;
						}
					}

					boost::add_edge(m, n, get(boost::edge_weight_t(), input_graph, boost::edge(m, n, input_graph).first), solution_graph); // add (m,n)
					predecessor[n] = m; // n has a new predecessor

					if (tagged[m] == true) { // if m is tagged
						to_be_tagged.insert(to_be_tagged.end(), n); // mark n to_be_tagged； n is the first one to be tagged in component_n
						if (tagged_value[m] > 0 && in_degree(m, solution_graph) > 2) {// update tagged_values of m when m is a non-group vertex newly become junction
							// update two tagged_values of m and its offspring long branch in component_m; it only makes this long branche shorter
							std::vector<int> to_be_updated;
							tagged_value[m] = 0;
							branch_begin[m] = m;
							boost::tie(ai, a_end) = boost::adjacent_vertices(m, solution_graph);
							for (; ai != a_end; ai++) {
								if (tagged_value[*ai] > 0 && *ai != predecessor[m]) { // m is non-group non-root, so it has a predecessor
									// if *ai is not group or junction vertex, you don't need to update it
									to_be_updated.insert(to_be_updated.end(), *ai); // tagged offsprings of m are to_be_updated
								}
							}
							for (int i = 0; i < to_be_updated.size(); i++) {
								tagged_value[to_be_updated[i]] = tagged_value[predecessor[to_be_updated[i]]] + 1;
								branch_begin[to_be_tagged[i]] = branch_begin[predecessor[to_be_updated[i]]];
								boost::tie(ai, a_end) = boost::adjacent_vertices(to_be_updated[i], solution_graph);
								for (; ai != a_end; ai++) {
									if (tagged_value[*ai] > 0 && *ai != predecessor[to_be_updated[i]]) {
										to_be_updated.insert(to_be_updated.end(), *ai);
									}
								}
							}

						}
					}

				}
				else {  // a new branch_begin; the previous branch cannot be replaced

					tagged[to_be_tagged[i]] = true; // tag to_be_tagged[i]
					tagged_value[to_be_tagged[i]] = 0;
					branch_begin[to_be_tagged[i]] = to_be_tagged[i];
					boost::tie(ai, a_end) = boost::adjacent_vertices(to_be_tagged[i], solution_graph);
					for (; ai != a_end; ai++) {
						if (tagged[*ai] == false) {
							predecessor[*ai] = to_be_tagged[i];
							to_be_tagged.insert(to_be_tagged.end(), *ai);
						}
					}

				}

			}
			else { // a new branch_begin; the previous branch is not long enough

				tagged[to_be_tagged[i]] = true; // tag to_be_tagged[i]
				tagged_value[to_be_tagged[i]] = 0;
				branch_begin[to_be_tagged[i]] = to_be_tagged[i];
				boost::tie(ai, a_end) = boost::adjacent_vertices(to_be_tagged[i], solution_graph);
				for (; ai != a_end; ai++) {
					if (tagged[*ai] == false) {
						predecessor[*ai] = to_be_tagged[i];
						to_be_tagged.insert(to_be_tagged.end(), *ai);
					}
				}

			}

		}
		else { // to_be_tagged[i] is neither a junction nor group vertex

			tagged[to_be_tagged[i]] = true; // tag to_be_tagged[i]
			tagged_value[to_be_tagged[i]] = tagged_value[predecessor[to_be_tagged[i]]] + 1;
			branch_begin[to_be_tagged[i]] = branch_begin[predecessor[to_be_tagged[i]]];
			boost::tie(ai, a_end) = boost::adjacent_vertices(to_be_tagged[i], solution_graph);
			for (; ai != a_end; ai++) {
				if (tagged[*ai] == false) {
					predecessor[*ai] = to_be_tagged[i];
					to_be_tagged.insert(to_be_tagged.end(), *ai);
				}
			}

		}

	}

	//// check whether all inside vertices have been tagged
	//for (int i = 0; i < included_vertices.size(); i++) {
	//	if (tagged[included_vertices[i]] == false) {
	//		cout << "untagged " << included_vertices[i] << endl;
	//	}
	//}
	//for (int i = 0; i < to_be_tagged.size(); i++) {
	//	cout << "to_be_tagged " << to_be_tagged[i] << endl;
	//}

	return solution_graph;

}
#pragma endregion branch_replacing


#pragma region
graph branch_replacing_NWFGSTP(graph input_graph, graph group_graph, graph solution_graph, std::vector<int>& included_vertices,
	int alpha, std::vector<int> LV) {

	if (num_edges(solution_graph) == 0) { // return solution_graph when it's empty
		return solution_graph;
	}

	int N = num_vertices(input_graph);

	typedef boost::graph_traits<graph>::adjacency_iterator AdjacencyIterator;
	AdjacencyIterator ai, a_end;
	AdjacencyIterator bi, b_end;
	typedef graph::edge_descriptor Edge;
	//srand(time(NULL)); //  seed random number generator

	// randomly select a inside group vertex as the root
	int N_group = num_vertices(group_graph) - N;
	int RAND = rand() % N_group; // random number 0,N_group-1; it's much slower to generate random vertex and then check it's in group or not
	boost::tie(ai, a_end) = boost::adjacent_vertices(N + RAND, group_graph);
	//cout << num_vertices(group_graph) << endl;
	//cout << N << endl;
	//cout << N_group << endl;
	//cout << RAND << endl;
	int root;
	for (; ai != a_end; ai++) {
		if (in_degree(*ai, solution_graph) > 0) {
			root = *ai;  // the first inside vertex in this random group is the root
			break;
		}
	}

	//cout << "root " << root << endl;

	std::vector<bool> tagged(N);
	std::vector<int> tagged_value(N); // corresponding to alpha
	std::vector<int> branch_begin(N);
	std::vector<int> predecessor(N);
	std::vector<int> to_be_tagged;

	tagged[root] = true; // tag root
	tagged_value[root] = 0;
	branch_begin[root] = root;
	boost::tie(ai, a_end) = boost::adjacent_vertices(root, solution_graph);
	for (; ai != a_end; ai++) {
		predecessor[*ai] = root; // every vertex in to_be_tagged has a predecessor
		to_be_tagged.insert(to_be_tagged.end(), *ai); // all adjacent vertices of root are to be tagged
	}
	for (int i = 0; i < to_be_tagged.size(); i++) { // all vertices in the solution will be tagged eventually

													//cout << "tagging " << to_be_tagged[i] << endl;
		if (in_degree(to_be_tagged[i], solution_graph) > 2 || in_degree(to_be_tagged[i], group_graph) > 0) { // to_be_tagged[i] is a junction or group vertex

			if (tagged_value[predecessor[to_be_tagged[i]]] >= alpha) { // a potential branch to_be_tagged[i],branch_begin[predecessor[to_be_tagged[i]]]

																	   // calculate branch_cost
				double branch_cost = 0;
				int v1 = to_be_tagged[i];
				int v2 = predecessor[to_be_tagged[i]];
				while (0 < 1) {
					branch_cost = branch_cost + get(boost::edge_weight_t(), input_graph, boost::edge(v1, v2, input_graph).first);
					if (v2 != branch_begin[v2]) {
						branch_cost = branch_cost - get(boost::vertex_name_t(), input_graph, v2); // v2 is in this branch
						v1 = v2;
						v2 = predecessor[v2];
					}
					else { // v2 is branch end
						break;
					}
				}

				// check component
				std::vector<int> component_m, component_n; // component_m is the root component (with v2 inside)
				boost::remove_edge(to_be_tagged[i], predecessor[to_be_tagged[i]], solution_graph); // component_n is isolated
				boost::remove_edge(v1, v2, solution_graph); // v2 = branch_begin[predecessor[to_be_tagged[i]]]; component_m is isolated
				std::vector<int> checked(N);
				std::vector<int> to_be_checked;
				component_m.insert(component_m.end(), v2); // v2 is in component_m
				checked[v2] = 1;
				boost::tie(ai, a_end) = boost::adjacent_vertices(v2, solution_graph);
				for (; ai != a_end; ai++) {
					component_m.insert(component_m.end(), *ai);
					to_be_checked.insert(to_be_checked.end(), *ai);
				}
				for (int j = 0; j < to_be_checked.size(); j++) {
					checked[to_be_checked[j]] = 1;
					boost::tie(ai, a_end) = boost::adjacent_vertices(to_be_checked[j], solution_graph);
					for (; ai != a_end; ai++) {
						if (checked[*ai] == 0) {
							component_m.insert(component_m.end(), *ai);
							to_be_checked.insert(to_be_checked.end(), *ai);
						}
					}
				}
				checked.clear();
				checked.resize(N);
				to_be_checked.clear();
				component_n.insert(component_n.end(), to_be_tagged[i]); // to_be_tagged[i] is in component_n
				checked[to_be_tagged[i]] = 1;
				boost::tie(ai, a_end) = boost::adjacent_vertices(to_be_tagged[i], solution_graph);
				for (; ai != a_end; ai++) {
					component_n.insert(component_n.end(), *ai);
					to_be_checked.insert(to_be_checked.end(), *ai);
				}
				for (int j = 0; j < to_be_checked.size(); j++) {
					checked[to_be_checked[j]] = 1;
					boost::tie(ai, a_end) = boost::adjacent_vertices(to_be_checked[j], solution_graph);
					for (; ai != a_end; ai++) {
						if (checked[*ai] == 0) {
							component_n.insert(component_n.end(), *ai);
							to_be_checked.insert(to_be_checked.end(), *ai);
						}
					}
				}
				// restore the two edges removed above
				boost::add_edge(to_be_tagged[i], predecessor[to_be_tagged[i]], get(boost::edge_weight_t(), input_graph,
					boost::edge(to_be_tagged[i], predecessor[to_be_tagged[i]], input_graph).first), solution_graph);
				boost::add_edge(v1, v2, get(boost::edge_weight_t(), input_graph, boost::edge(v1, v2, input_graph).first), solution_graph);

				// try to find the minimum-cost edge (m,n) to replace branch
				int m, n; // m in the root component, it may be untagged; n in the other compomnent, it must be untagged
				double c_mn = 1e9;
				for (int e1 = 0; e1 < component_m.size(); e1++) {
					for (int e2 = 0; e2 < component_n.size(); e2++) {
						pair<Edge, bool> ed = boost::edge(component_m[e1], component_n[e2], input_graph);
						if (ed.second) { // this edge exist
							double edge_cost =
								get(boost::edge_weight_t(), input_graph, boost::edge(component_m[e1], component_n[e2], input_graph).first);
							if (edge_cost < c_mn && LV[component_m[e1]] == 0 && LV[component_m[e2]] == 0) {
								// it won't turn leaf vertices as non-leaves
								c_mn = edge_cost;
								m = component_m[e1];
								n = component_n[e2];
							}
						}
					}
				}


				if (c_mn < branch_cost) { // use (m,n) to replace branch

										  //cout << "BRA add " << m << "," << n << ": " << c_mn << endl;

										  // remove branch
					v1 = to_be_tagged[i];
					v2 = predecessor[to_be_tagged[i]];
					while (0 < 1) {
						boost::remove_edge(v1, v2, solution_graph);
						//cout << "BRA remove " << v1 << "," << v2 << endl;
						if (v2 != branch_begin[v2]) {
							remove_included_vertices(included_vertices, { v2 }); // remove inside vertices
							v1 = v2;
							v2 = predecessor[v2];
						}
						else {
							break;
						}
					}

					boost::add_edge(m, n, get(boost::edge_weight_t(), input_graph, boost::edge(m, n, input_graph).first), solution_graph); // add (m,n)
					predecessor[n] = m; // n has a new predecessor

					if (tagged[m] == true) { // if m is tagged
						to_be_tagged.insert(to_be_tagged.end(), n); // mark n to_be_tagged； n is the first one to be tagged in component_n
						if (tagged_value[m] > 0 && in_degree(m, solution_graph) > 2) {// update tagged_values of m when m is a non-group vertex newly become junction
																					  // update two tagged_values of m and its offspring long branch in component_m; it only makes this long branche shorter
							std::vector<int> to_be_updated;
							tagged_value[m] = 0;
							branch_begin[m] = m;
							boost::tie(ai, a_end) = boost::adjacent_vertices(m, solution_graph);
							for (; ai != a_end; ai++) {
								if (tagged_value[*ai] > 0 && *ai != predecessor[m]) { // m is non-group non-root, so it has a predecessor
																					  // if *ai is not group or junction vertex, you don't need to update it
									to_be_updated.insert(to_be_updated.end(), *ai); // tagged offsprings of m are to_be_updated
								}
							}
							for (int i = 0; i < to_be_updated.size(); i++) {
								tagged_value[to_be_updated[i]] = tagged_value[predecessor[to_be_updated[i]]] + 1;
								branch_begin[to_be_tagged[i]] = branch_begin[predecessor[to_be_updated[i]]];
								boost::tie(ai, a_end) = boost::adjacent_vertices(to_be_updated[i], solution_graph);
								for (; ai != a_end; ai++) {
									if (tagged_value[*ai] > 0 && *ai != predecessor[to_be_updated[i]]) {
										to_be_updated.insert(to_be_updated.end(), *ai);
									}
								}
							}

						}
					}

				}
				else {  // a new branch_begin; the previous branch cannot be replaced

					tagged[to_be_tagged[i]] = true; // tag to_be_tagged[i]
					tagged_value[to_be_tagged[i]] = 0;
					branch_begin[to_be_tagged[i]] = to_be_tagged[i];
					boost::tie(ai, a_end) = boost::adjacent_vertices(to_be_tagged[i], solution_graph);
					for (; ai != a_end; ai++) {
						if (tagged[*ai] == false) {
							predecessor[*ai] = to_be_tagged[i];
							to_be_tagged.insert(to_be_tagged.end(), *ai);
						}
					}

				}

			}
			else { // a new branch_begin; the previous branch is not long enough

				tagged[to_be_tagged[i]] = true; // tag to_be_tagged[i]
				tagged_value[to_be_tagged[i]] = 0;
				branch_begin[to_be_tagged[i]] = to_be_tagged[i];
				boost::tie(ai, a_end) = boost::adjacent_vertices(to_be_tagged[i], solution_graph);
				for (; ai != a_end; ai++) {
					if (tagged[*ai] == false) {
						predecessor[*ai] = to_be_tagged[i];
						to_be_tagged.insert(to_be_tagged.end(), *ai);
					}
				}

			}

		}
		else { // to_be_tagged[i] is neither a junction nor group vertex

			tagged[to_be_tagged[i]] = true; // tag to_be_tagged[i]
			tagged_value[to_be_tagged[i]] = tagged_value[predecessor[to_be_tagged[i]]] + 1;
			branch_begin[to_be_tagged[i]] = branch_begin[predecessor[to_be_tagged[i]]];
			boost::tie(ai, a_end) = boost::adjacent_vertices(to_be_tagged[i], solution_graph);
			for (; ai != a_end; ai++) {
				if (tagged[*ai] == false) {
					predecessor[*ai] = to_be_tagged[i];
					to_be_tagged.insert(to_be_tagged.end(), *ai);
				}
			}

		}

	}

	//// check whether all inside vertices have been tagged
	//for (int i = 0; i < included_vertices.size(); i++) {
	//	if (tagged[included_vertices[i]] == false) {
	//		cout << "untagged " << included_vertices[i] << endl;
	//	}
	//}
	//for (int i = 0; i < to_be_tagged.size(); i++) {
	//	cout << "to_be_tagged " << to_be_tagged[i] << endl;
	//}

	return solution_graph;

}
#pragma endregion branch_replacing_NWFGSTP


#pragma region
graph group_pruning(graph input_graph, graph group_graph, graph solution_graph, std::vector<int>& included_vertices) {

	if (num_edges(solution_graph) == 0) { // return solution_graph when it's empty
		return solution_graph;
	}

	int N = num_vertices(input_graph);
	int N_group = num_vertices(group_graph) - N;

	typedef boost::graph_traits<graph>::adjacency_iterator AdjacencyIterator;
	AdjacencyIterator ai, a_end;
	AdjacencyIterator bi, b_end;

	int root;

	// check compulsory_terminal; there are edges in solution_graph
	bool compulsory_terminal_exist = false;
	for (int i = 0; i < N_group; i++) {
		boost::tie(ai, a_end) = boost::adjacent_vertices(N + i, group_graph); // vertices in group i
		int vnum_in_solution = 0;
		int x;
		for (; ai != a_end; ai++) {
			if (in_degree(*ai, solution_graph) > 0) {  // there are edges in solution_graph
				vnum_in_solution++; // the number of vertices in the solution that are in group i
				x = *ai;
			}
		}
		if (vnum_in_solution == 1) { // it's a compulsory_terminal
			compulsory_terminal_exist = true;
			root = x; // mark it as the root
			break;
		}
	}

	pairing_heap<node_max_heap> PQ;
	node_max_heap node0;


	// pruning to find a compulsory_terminal 
	if (compulsory_terminal_exist == false) { // there is no compulsory_terminal

		std::vector<int> unchecked_leaves;
		for (int i = 0; i < included_vertices.size(); i++) { // included_vertices is now correct, but not later
			if (in_degree(included_vertices[i], solution_graph) == 1) {
				unchecked_leaves.insert(unchecked_leaves.end(), included_vertices[i]); // unchecked_leaves initially contains all leaves
			}
		}

		//cout << "unchecked_leaves.size() " << unchecked_leaves.size() << endl;

		while (compulsory_terminal_exist == false) { // while there is no compulsory_terminal


			while (unchecked_leaves.size() > 0) { // check unchecked_leaves

				if (in_degree(unchecked_leaves[0], group_graph) > 0) { // unchecked_leaves[0] is a group vertex
					boost::tie(ai, a_end) = boost::adjacent_vertices(unchecked_leaves[0], solution_graph);
					node0.index = unchecked_leaves[0];
					node0.priority_value = get(boost::edge_weight_t(), input_graph, boost::edge(unchecked_leaves[0], *ai, input_graph).first)
						- get(boost::vertex_name_t(), input_graph, unchecked_leaves[0]);
					PQ.push(node0); // a group leaf is pushed into PQ
				}
				else { // unchecked_leaves[0] is not a group vertex
					bool group_junction_predecessor_found = false;
					int predecessor, predecessor_adjacent;
					boost::tie(ai, a_end) = boost::adjacent_vertices(unchecked_leaves[0], solution_graph);
					predecessor_adjacent = unchecked_leaves[0];
					predecessor = *ai;
					while (group_junction_predecessor_found == false) {
						if (in_degree(predecessor, group_graph) > 0 ||
							in_degree(predecessor, solution_graph) > 2) {// this predecessor is group_junction_predecessor; predecessor is in the solution
							group_junction_predecessor_found = true;
						}
						else {
							boost::tie(ai, a_end) = boost::adjacent_vertices(predecessor, solution_graph);
							for (; ai != a_end; ai++) {
								if (*ai != predecessor_adjacent) {
									predecessor_adjacent = predecessor;
									predecessor = *ai; // the new predecessor
									break;
								}
							}
						}
					}
					boost::remove_edge(predecessor, predecessor_adjacent, solution_graph); // disconnected this branch; disconnected vertices are non-group
					//cout << "remove " << predecessor << "," << predecessor_adjacent << endl;
					if (in_degree(predecessor, solution_graph) == 1) { // predecessor is a new group leaf; predecessor is in the solution
						boost::tie(ai, a_end) = boost::adjacent_vertices(predecessor, solution_graph);
						node0.index = predecessor;
						node0.priority_value = get(boost::edge_weight_t(), input_graph, boost::edge(predecessor, *ai, input_graph).first)
							- get(boost::vertex_name_t(), input_graph, predecessor);
						PQ.push(node0); // this new group leaf is pushed into PQ; this new group leaf is definitely not compulsory
					}

				}
				unchecked_leaves.erase(unchecked_leaves.begin()); // unchecked_leaves[0] has been checked

			}

			//cout << "PQ.size() " << PQ.size() << endl;

			// prune top edge; PQ.size() must be larger than 1, or compulsory_terminal_exist
			if (in_degree(PQ.top().index, solution_graph) > 0) { // PQ.top().index may be the only vertex in solution_graph, when *ai cause errors
				boost::tie(ai, a_end) = boost::adjacent_vertices(PQ.top().index, solution_graph);
				boost::remove_edge(PQ.top().index, *ai, solution_graph); // prune this leaf from solution_graph; included_vertices is not correct any more
				//cout << "remove " << PQ.top().index << "," << *ai << endl;
				if (in_degree(*ai, solution_graph) == 1) { // *ai is a new leaf; *ai is definitely in the solution
					unchecked_leaves.insert(unchecked_leaves.end(), *ai); // mark *ai as unchecked
				}
			}


			// check compulsory_terminal_exist; PQ.size()>=1
			if (PQ.size() + unchecked_leaves.size() == 1) { // solution_graph is a single vertex
				compulsory_terminal_exist = true;
				root = PQ.top().index; // mark it as the root
				//cout << "return solution_graph" << endl;
				// return solution_graph
				for (int i = 0; i < N; i++) {
					if (in_degree(i, solution_graph) > 0) {
						clear_vertex(i, solution_graph);
					}
				}
				included_vertices.clear();
				included_vertices.insert(included_vertices.end(), root);
				return solution_graph;
			}
			else { // solution_graph has edges
				boost::tie(ai, a_end) = boost::adjacent_vertices(PQ.top().index, group_graph); // the groups of PQ.top().index
				for (; ai != a_end; ai++) { // a group containing PQ.top().index
					int vnum_in_solution = 0;
					int x;
					boost::tie(bi, b_end) = boost::adjacent_vertices(*ai, group_graph); // the vertices in this group
					for (; bi != b_end; bi++) {
						if (in_degree(*bi, solution_graph) > 0) { // all disconnected vertices in solution_graph are non-group
							vnum_in_solution++;
							x = *bi;
						}
					}
					if (vnum_in_solution == 1) { // only one vertex in this group is in the solution
						compulsory_terminal_exist = true;
						root = x; // mark it as the root
						break;
					}
				}
			}

			PQ.pop(); // pop out top leaf

		}

	}





	//cout << "Root: " << root << endl;

	// there are edges in the solution; or solution will be returned before
	std::vector<bool> tagged(N);
	std::vector<int> tagged_value(N); // corresponding to alpha
	std::vector<int> to_be_tagged;
	std::vector<int> unchecked_leaves; // initially mark all leaves as unchecked_leaves
	tagged[root] = true;
	tagged_value[root] = 0;
	if (in_degree(root, solution_graph) == 1) { // root is definitely in the solution
		unchecked_leaves.insert(unchecked_leaves.end(), root); // unchecked_leaves initially contains all leaves
	}
	boost::tie(ai, a_end) = boost::adjacent_vertices(root, solution_graph);
	for (; ai != a_end; ai++) {
		to_be_tagged.insert(to_be_tagged.end(), *ai); // all adjacent vertices of root are to be tagged
	}
	for (int i = 0; i < to_be_tagged.size(); i++) {
		boost::tie(ai, a_end) = boost::adjacent_vertices(to_be_tagged[i], solution_graph);
		for (; ai != a_end; ai++) {
			if (tagged[*ai] == false) {
				to_be_tagged.insert(to_be_tagged.end(), *ai); // new to_be_tagged
			}
			else { // *ai is the predecessor of to_be_tagged[i]
				//cout << *ai << " is predecessor of " << to_be_tagged[i] << endl;
				tagged[to_be_tagged[i]] = true; // tag to_be_tagged[i]
				if (in_degree(*ai, solution_graph) > 2 || in_degree(*ai, group_graph) > 0) { // *ai is junction or group vertex in the solution
					tagged_value[to_be_tagged[i]] = get(boost::edge_weight_t(), input_graph, boost::edge(to_be_tagged[i], *ai, input_graph).first) -
						get(boost::vertex_name_t(), input_graph, to_be_tagged[i]);
				}
				else {
					tagged_value[to_be_tagged[i]] = tagged_value[*ai] +
						get(boost::edge_weight_t(), input_graph, boost::edge(to_be_tagged[i], *ai, input_graph).first) -
						get(boost::vertex_name_t(), input_graph, to_be_tagged[i]);
				}
				//break; // Wrong! even though *ai is unique, you can't use break since new to_be_tagged need to be added
			}
		}
		if (in_degree(to_be_tagged[i], solution_graph) == 1) { // to_be_tagged[i] is in the solution
			unchecked_leaves.insert(unchecked_leaves.end(), to_be_tagged[i]); // unchecked_leaves initially contains all leaves
		}
	}



	// there are edges in the solution; or solution will be returned before
	PQ.clear();
	int times = 0;
	std::vector<int> newly_generated_compulsory_terminals(N);
	while (PQ.size() > 0 || unchecked_leaves.size() > 0) { // if these two values equal 0, all leaves are compulsory
		times++;
		while (unchecked_leaves.size() > 0) {

			if (in_degree(unchecked_leaves[0], group_graph) > 0) { // unchecked_leaves[0] is a group vertex in the solution

				// check whether unchecked_leaves[0] is compulsory
				bool is_compulsory = false;
				boost::tie(ai, a_end) = boost::adjacent_vertices(unchecked_leaves[0], group_graph); // the groups of unchecked_leaves[0]
				for (; ai != a_end; ai++) { // a group containing unchecked_leaves[0]
					int vnum_in_solution = 0;
					int x;
					boost::tie(bi, b_end) = boost::adjacent_vertices(*ai, group_graph); // the vertices in this group
					for (; bi != b_end; bi++) {
						if (in_degree(*bi, solution_graph) > 0) { // all disconnected vertices in solution_graph are non-group, so *bi is in the solution
							vnum_in_solution++;
							x = *bi;
						}
					}
					if (vnum_in_solution == 1) { // only one vertex (unchecked_leaves[0]) in this group is in the solution
						is_compulsory = true;
						break;
					}
				}
				if (is_compulsory == true) { // unchecked_leaves[0] is compulsory
				}
				else { // unchecked_leaves[0] is not compulsory
					node0.index = unchecked_leaves[0];
					node0.priority_value = tagged_value[unchecked_leaves[0]];
					PQ.push(node0); // push unchecked_leaves[0] into PQ
				}

			}
			else { // unchecked_leaves[0] is not a group vertex
				bool group_junction_predecessor_found = false;
				int predecessor, predecessor_adjacent;
				boost::tie(ai, a_end) = boost::adjacent_vertices(unchecked_leaves[0], solution_graph);
				predecessor_adjacent = unchecked_leaves[0];
				predecessor = *ai;
				while (group_junction_predecessor_found == false) {
					if (in_degree(predecessor, group_graph) > 0 ||
						in_degree(predecessor, solution_graph) > 2) {// this predecessor is group_junction_predecessor in the solution
						group_junction_predecessor_found = true;
					}
					else {
						boost::tie(ai, a_end) = boost::adjacent_vertices(predecessor, solution_graph);
						for (; ai != a_end; ai++) {
							if (*ai != predecessor_adjacent) {
								predecessor_adjacent = predecessor;
								predecessor = *ai; // the new predecessor
								break;
							}
						}
					}
				}
				boost::remove_edge(predecessor, predecessor_adjacent, solution_graph); // disconnected this non-group branch
				if (in_degree(predecessor, solution_graph) == 1) { // predecessor is a new group leaf
					unchecked_leaves.insert(unchecked_leaves.end(), predecessor); // you cann't push predecessor into PQ since it may be old compulsory
				}
			}
			unchecked_leaves.erase(unchecked_leaves.begin()); // unchecked_leaves[0] has been checked

		}

		if (PQ.size() > 0) { // or solution is already fully pruned; PQ contains non-compulsory group leaves; if PQ.size() > 0, then there are edges in solution

			if (times == 1) { // all elements in PQ are non-compulsory group leaves
				// prune top edge
				boost::tie(ai, a_end) = boost::adjacent_vertices(PQ.top().index, solution_graph); // PQ.top().index is in the solution
				boost::remove_edge(PQ.top().index, *ai, solution_graph); // prune this leaf from solution_graph
				//cout << "Prune " << PQ.top().index << "," << *ai << endl;
				if (in_degree(*ai, solution_graph) == 1) { // *ai is a new leaf in the solution
					unchecked_leaves.insert(unchecked_leaves.end(), *ai); // mark *ai as unchecked
				}
				else if (in_degree(*ai, solution_graph) == 0) { // solution only contains the single vertex *ai after removing edges
					// return solution_graph
					for (int i = 0; i < N; i++) {
						if (in_degree(i, solution_graph) > 0) {
							clear_vertex(i, solution_graph);
						}
					}
					included_vertices.clear();
					included_vertices.insert(included_vertices.end(), root); // *ai is the root
					return solution_graph;
				}
				// there are edges in the solution
				boost::tie(ai, a_end) = boost::adjacent_vertices(PQ.top().index, group_graph); // the groups of PQ.top().index
				for (; ai != a_end; ai++) { // a group containing PQ.top().index
					int vnum_in_solution = 0;
					int x;
					boost::tie(bi, b_end) = boost::adjacent_vertices(*ai, group_graph); // the vertices in this group
					for (; bi != b_end; bi++) {
						if (in_degree(*bi, solution_graph) > 0) {// all disconnected edges in solution_graph are non-group, so *bi is in the solution
							vnum_in_solution++;
							x = *bi;
						}
					}
					if (vnum_in_solution == 1) { // only one vertex (x) in this group is in the solution
						newly_generated_compulsory_terminals[x] = 1; // a newly_generated_compulsory_terminal	
					} // it cannot be old compulsory_terminals since they cannnot share groups with PQ.top().index
				}
				PQ.pop(); // pop out top leaf
			}
			else { // elements in PQ may be compulsory

				if (newly_generated_compulsory_terminals[PQ.top().index] == 0) { // PQ.top().index is not a newly_generated_compulsory_terminal
					// prune top edge
					boost::tie(ai, a_end) = boost::adjacent_vertices(PQ.top().index, solution_graph);
					boost::remove_edge(PQ.top().index, *ai, solution_graph); // prune this leaf from solution_graph
					//cout << "Prune1 " << PQ.top().index << "," << *ai << endl;
					if (in_degree(*ai, solution_graph) == 1) { // *ai is a new leaf in the solution
						unchecked_leaves.insert(unchecked_leaves.end(), *ai); // mark *ai as unchecked
					}
					else if (in_degree(*ai, solution_graph) == 0) { // solution only contains the single vertex *ai after removing edges
						// return solution_graph
						for (int i = 0; i < N; i++) {
							if (in_degree(i, solution_graph) > 0) {
								clear_vertex(i, solution_graph);
							}
						}
						included_vertices.clear();
						included_vertices.insert(included_vertices.end(), root); // *ai is the root
						return solution_graph;
					}
					// there are edges in the solution
					boost::tie(ai, a_end) = boost::adjacent_vertices(PQ.top().index, group_graph); // the groups of PQ.top().index
					for (; ai != a_end; ai++) { // a group containing PQ.top().index
						int vnum_in_solution = 0;
						int x;
						boost::tie(bi, b_end) = boost::adjacent_vertices(*ai, group_graph); // the vertices in this group
						for (; bi != b_end; bi++) {
							if (in_degree(*bi, solution_graph) > 0) {// all disconnected edges in solution_graph are non-group, so *bi is in the solution
								vnum_in_solution++;
								x = *bi;
							}
						}
						if (vnum_in_solution == 1) { // only one vertex (x) in this group is in the solution
							newly_generated_compulsory_terminals[x] = 1; // a newly_generated_compulsory_terminal
						}
					}
				}
				PQ.pop(); // pop out top leaf
			}

		}

	}



	// update included_vertices
	std::vector<bool> touched(N);
	std::vector<int> to_be_touched;
	included_vertices.clear();
	touched[root] = true;
	std::vector<int> included(N); // it has advantages over included_vertices since included[i] can be easily checked
	included[root] = 1; // root is included
	included_vertices.insert(included_vertices.end(), root);
	boost::tie(ai, a_end) = boost::adjacent_vertices(root, solution_graph);
	for (; ai != a_end; ai++) {
		to_be_touched.insert(to_be_touched.end(), *ai); // all adjacent vertices of root are to_be_touched
	}
	for (int i = 0; i < to_be_touched.size(); i++) {
		boost::tie(ai, a_end) = boost::adjacent_vertices(to_be_touched[i], solution_graph);
		for (; ai != a_end; ai++) {
			if (touched[*ai] == false) {
				to_be_touched.insert(to_be_touched.end(), *ai); // new to_be_touched
			}
		}
		touched[to_be_touched[i]] = true; // touch to_be_touched[i]
		included[to_be_touched[i]] = 1;
		included_vertices.insert(included_vertices.end(), to_be_touched[i]);
	}
	sort(included_vertices.begin(), included_vertices.end(), compare1); // sort included_vertices

	// remove disconnected edges
	for (int i = 0; i < N; i++) {
		if (in_degree(i, solution_graph) > 0 && included[i] == 0) {
			clear_vertex(i, solution_graph);
		}
	}


	return solution_graph;

}
#pragma endregion group_pruning



#pragma region
void single_vertex_solution_check(graph input_graph, graph group_graph, graph solution_graph, std::vector<int>& included_vertices) {

	// in the Steiner tree techniques, we assume solution_graph has edges. If not, they may return wrong included_vertices; this code is to safeguard included_vertices

	int N = num_vertices(solution_graph);
	int N_group = num_vertices(group_graph) - N;

	if (num_edges(solution_graph) == 0) {

		double max_nw = -1e8;
		int solution_vertex;
		for (int i = 0; i < N; i++) {
			if (in_degree(i, group_graph) == N_group) { // this vertex is contained by every group, and thus is a feasible solution
				double i_nw = get(boost::vertex_name_t(), input_graph, i);
				if (i_nw > max_nw) {
					max_nw = i_nw;
					solution_vertex = i;
				}
			}
		}
		included_vertices.clear();
		included_vertices.insert(included_vertices.end(), solution_vertex); // solution_vertex is the feasible solution with the largest nw
	}


}
#pragma endregion single_vertex_solution_check


#pragma region 

graph find_MST_Yahui_withoutTimeing(graph input_graph) {

	int N = num_vertices(input_graph);
	graph output_graph(N);
	for (int i = 0; i < N; i++) {
		boost::put(boost::vertex_name_t(), output_graph, i, get(boost::vertex_name_t(), input_graph, i)); // put inside the node weight
	}
	std::vector <boost::graph_traits<graph>::vertex_descriptor> p(N); // minimum_spanning_tree traits

	if (in_degree(0, input_graph) > 0) { // 0 is connected
		// find minimum_spanning_tree
		prim_minimum_spanning_tree(input_graph, &p[0]); // it can only be &p[0], and 0 must be connected in MST;
		// print edges in minimum_spanning_tree
		for (int i = 1; i != p.size(); ++i) { // p[0]=0;
			if (p[i] != i) {
				boost::add_edge(i, p[i], get(boost::edge_weight_t(), input_graph, boost::edge(i, p[i], input_graph).first), output_graph); // add edge
			}
		}
	}
	else { // 0 is disconnected
		int v1 = 0;
		for (int i = 1; i < N; i++) {
			if (in_degree(i, input_graph) > 0) {
				v1 = i;
				break;
			}
		}
		boost::add_edge(0, v1, 1, input_graph); // add edge (0,v1)
												// find minimum_spanning_tree
		prim_minimum_spanning_tree(input_graph, &p[0]); // it can only be &p[0]; if 0 is disconnected, you need a fake edge to connect it
														// print edges in minimum_spanning_tree
		for (int i = 1; i != p.size(); ++i) { // p[0]=0;
			if (p[i] != i) {
				boost::add_edge(i, p[i], get(boost::edge_weight_t(), input_graph, boost::edge(i, p[i], input_graph).first), output_graph); // add edge
			}
		}
		boost::remove_edge(0, v1, output_graph); // remove edge (0,v1)
	}

	return output_graph;
}

#pragma endregion find_MST_Yahui_withoutTimeing 2018年5月17日15:04:52


#pragma region 

void MST_P3_Yahui_withoutTimeing(graph input_graph, graph& solu_graph) {

	if (num_edges(solu_graph) <= 1) {
	}
	else {


		int N = num_vertices(input_graph);
		//graph base_graph = input_graph;
		//for (int i = 0; i < N; i++) {
		//	if (in_degree(i, solu_graph) == 0) {
		//		clear_vertex(i, base_graph); // remove unrelated edges; this is much slower than the version below
		//	}
		//}
		graph base_graph;
		for (int i = 0; i < N; i++) {
			boost::add_vertex(i, base_graph);
			boost::put(boost::vertex_name_t(), base_graph, i, get(boost::vertex_name_t(), input_graph, i)); // input node weight
		}
		graph::out_edge_iterator eit, eend;
		for (int i = 0; i < N; i++) {
			if (in_degree(i, solu_graph) >= 1) { // i is in solu_graph
				tie(eit, eend) = boost::out_edges(i, input_graph); // adjacent_vertices of i in input_graph
				for_each(eit, eend,
					[&input_graph, &i, &base_graph, &solu_graph](graph::edge_descriptor it)
				{
					int j = boost::target(it, input_graph);
					if (i > j && in_degree(j, solu_graph) > 0) { // j is in solu_graph
						boost::add_edge(i, j, get(boost::edge_weight_t(), input_graph, boost::edge(i, j, input_graph).first), base_graph); // input edge 
					}
				});
			}
		}

		base_graph = find_MST_Yahui_withoutTimeing(base_graph);
		solu_graph = base_graph;
	}
}

#pragma endregion MST_P3_Yahui_withoutTimeing  2018年1月21日14:39:46


#pragma region 

void MFSTA(graph input_graph, graph& solu_graph, std::vector<int> LV) {

	if (num_edges(solu_graph) <= 1) {
	}
	else {


		int N = num_vertices(input_graph);
		//graph base_graph = input_graph;
		//for (int i = 0; i < N; i++) {
		//	if (in_degree(i, solu_graph) == 0) {
		//		clear_vertex(i, base_graph); // remove unrelated edges; this is much slower than the version below
		//	}
		//}
		graph base_graph;
		for (int i = 0; i < N; i++) {
			boost::add_vertex(i, base_graph);
			boost::put(boost::vertex_name_t(), base_graph, i, get(boost::vertex_name_t(), input_graph, i)); // input node weight
		}
		graph::out_edge_iterator eit, eend;
		for (int i = 0; i < N; i++) {
			if (in_degree(i, solu_graph) >= 1) { // i is in solu_graph
				tie(eit, eend) = boost::out_edges(i, input_graph); // adjacent_vertices of i in input_graph
				for_each(eit, eend,
					[&input_graph, &i, &base_graph, &solu_graph, &LV](graph::edge_descriptor it)
				{
					int j = boost::target(it, input_graph);
					if (i > j && in_degree(j, solu_graph) > 0) { // j is in solu_graph
						if (LV[i] + LV[j] == 1) {
							boost::add_edge(i, j, get(boost::edge_weight_t(), input_graph, boost::edge(i, j, input_graph).first) + 1e9, base_graph); // large edge costs
						}
						else if (LV[i] + LV[j] == 2) {
							boost::add_edge(i, j, get(boost::edge_weight_t(), input_graph, boost::edge(i, j, input_graph).first) + 2e9, base_graph); // large edge costs
						}
						else {
							boost::add_edge(i, j, get(boost::edge_weight_t(), input_graph, boost::edge(i, j, input_graph).first), base_graph); // input edge 
						}

					}
				});
			}
		}

		base_graph = find_MST_Yahui_withoutTimeing(base_graph);

		// change large edge costs back
		typedef boost::graph_traits<graph>::adjacency_iterator AdjacencyIterator;
		AdjacencyIterator ai, a_end;
		typedef graph::edge_descriptor Edge;
		for (int i = 0; i < N; i++) {
			if (in_degree(i, base_graph) >= 1) {
				boost::tie(ai, a_end) = boost::adjacent_vertices(i, base_graph);
				for (; ai != a_end; ai++) {
					pair<Edge, bool> ed = boost::edge(i, *ai, base_graph);
					if (get(boost::edge_weight_t(), base_graph, ed.first) >= 1e9) { // large edge costs
						float new_weight = get(boost::edge_weight_t(), input_graph, boost::edge(i, *ai, input_graph).first);
						boost::put(boost::edge_weight_t(), base_graph, ed.first, new_weight);
					}
				}
			}
		}


		solu_graph = base_graph;
	}
}

#pragma endregion MFSTA


#pragma region 
graph MPA(graph input_graph, graph group_graph, std::vector<int>& included_vertices) {

	typedef boost::graph_traits<graph>::adjacency_iterator AdjacencyIterator;
	AdjacencyIterator ai, a_end;
	typedef graph::edge_descriptor Edge;

	int N = num_vertices(input_graph);

	// graph G_dash
	graph G_dash = copy_graph(input_graph);
	for (int i = 0; i < N; i++) {
		boost::tie(ai, a_end) = boost::adjacent_vertices(i, G_dash);
		for (; ai != a_end; ai++) {
			if (*ai > i) {
				double new_cost = get(boost::edge_weight_t(), G_dash, boost::edge(i, *ai, G_dash).first)
					- get(boost::vertex_name_t(), G_dash, i) - get(boost::vertex_name_t(), G_dash, *ai); // edge costs in G'
				boost::put(boost::edge_weight_t(), G_dash, boost::edge(i, *ai, G_dash).first, new_cost); // update edge costs
			}
		}
	}



	// find minimum_spanning_tree; we assume that input_graph is connected
	graph MST(N);
	for (int i = 0; i < N; i++) {
		boost::put(boost::vertex_name_t(), MST, i, get(boost::vertex_name_t(), input_graph, i)); // put inside the node weight
	}
	std::vector <boost::graph_traits<graph>::vertex_descriptor> p(N); // minimum_spanning_tree traits																  
	prim_minimum_spanning_tree(G_dash, &p[0]); // MST in G_dash; it can only be &p[0], and 0 must be connected in MST;							
	for (int i = 1; i != p.size(); ++i) { // p[0]=0;
		if (p[i] != i) {
			boost::add_edge(i, p[i], get(boost::edge_weight_t(), input_graph, boost::edge(i, p[i], input_graph).first), MST); // print edges (old costs)
		}
	}

	//cout << "here 1" << endl;

	//boost::property_map<graph, boost::edge_weight_t>::type EdgeWeightMap = get(boost::edge_weight_t(), MST);
	//typedef boost::graph_traits<graph>::edge_iterator edge_iter;
	//pair<edge_iter, edge_iter> edgePair;
	//for (edgePair = edges(MST); edgePair.first != edgePair.second; ++edgePair.first)
	//{
	//	cout << *edgePair.first << " "; // print edge
	//	cout << EdgeWeightMap[*edgePair.first] << endl; // print edge weight
	//}


	included_vertices.clear();
	for (int i = 0; i < N; i++) {
		included_vertices.insert(included_vertices.end(), i);  // update included_vertices
	}
	graph PostP_tree = group_pruning(input_graph, group_graph, MST, included_vertices);

	return PostP_tree;

	//cout << "here 2" << endl;

}
#pragma endregion MPA


#pragma region 
graph MPA_wihtout_G1(graph input_graph, graph group_graph, std::vector<int>& included_vertices) {

	typedef boost::graph_traits<graph>::adjacency_iterator AdjacencyIterator;
	AdjacencyIterator ai, a_end;
	typedef graph::edge_descriptor Edge;

	int N = num_vertices(input_graph);

	// find minimum_spanning_tree; we assume that input_graph is connected
	graph MST(N);
	for (int i = 0; i < N; i++) {
		boost::put(boost::vertex_name_t(), MST, i, get(boost::vertex_name_t(), input_graph, i)); // put inside the node weight
	}
	std::vector <boost::graph_traits<graph>::vertex_descriptor> p(N); // minimum_spanning_tree traits																  
	prim_minimum_spanning_tree(input_graph, &p[0]); // MST in G_dash; it can only be &p[0], and 0 must be connected in MST;							
	for (int i = 1; i != p.size(); ++i) { // p[0]=0;
		if (p[i] != i) {
			boost::add_edge(i, p[i], get(boost::edge_weight_t(), input_graph, boost::edge(i, p[i], input_graph).first), MST); // print edges (old costs)
		}
	}

	//cout << "here 1" << endl;

	//boost::property_map<graph, boost::edge_weight_t>::type EdgeWeightMap = get(boost::edge_weight_t(), MST);
	//typedef boost::graph_traits<graph>::edge_iterator edge_iter;
	//pair<edge_iter, edge_iter> edgePair;
	//for (edgePair = edges(MST); edgePair.first != edgePair.second; ++edgePair.first)
	//{
	//	cout << *edgePair.first << " "; // print edge
	//	cout << EdgeWeightMap[*edgePair.first] << endl; // print edge weight
	//}


	included_vertices.clear();
	for (int i = 0; i < N; i++) {
		included_vertices.insert(included_vertices.end(), i);  // update included_vertices
	}
	graph PostP_tree = group_pruning(input_graph, group_graph, MST, included_vertices);

	return PostP_tree;

	//cout << "here 2" << endl;

}
#pragma endregion MPA_wihtout_G1


#pragma region 
graph MPA_NWFGSTP(graph input_graph, graph group_graph, std::vector<int>& included_vertices, std::vector<int> LV) {

	typedef boost::graph_traits<graph>::adjacency_iterator AdjacencyIterator;
	AdjacencyIterator ai, a_end;
	typedef graph::edge_descriptor Edge;

	int N = num_vertices(input_graph);

	// graph G_dash
	graph G_dash = copy_graph(input_graph);
	for (int i = 0; i < N; i++) {
		boost::tie(ai, a_end) = boost::adjacent_vertices(i, G_dash);
		for (; ai != a_end; ai++) {
			if (*ai > i) {
				double new_cost = get(boost::edge_weight_t(), G_dash, boost::edge(i, *ai, G_dash).first)
					- get(boost::vertex_name_t(), G_dash, i) - get(boost::vertex_name_t(), G_dash, *ai); // edge costs in G'
				boost::put(boost::edge_weight_t(), G_dash, boost::edge(i, *ai, G_dash).first, new_cost); // update edge costs
			}
		}
	}


	// change large edge costs back
	for (int i = 0; i < N; i++) {
		if (LV[i] == 1) {
			boost::tie(ai, a_end) = boost::adjacent_vertices(i, G_dash);
			for (; ai != a_end; ai++) {
				pair<Edge, bool> ed = boost::edge(i, *ai, G_dash);
				float new_weight = get(boost::edge_weight_t(), G_dash, ed.first) + 1e9;
				boost::put(boost::edge_weight_t(), G_dash, ed.first, new_weight);
			}
		}
	}



	// find minimum_spanning_tree; we assume that input_graph is connected
	graph MST(N);
	for (int i = 0; i < N; i++) {
		boost::put(boost::vertex_name_t(), MST, i, get(boost::vertex_name_t(), input_graph, i)); // put inside the node weight
	}
	std::vector <boost::graph_traits<graph>::vertex_descriptor> p(N); // minimum_spanning_tree traits																  
	prim_minimum_spanning_tree(G_dash, &p[0]); // MST in G_dash; it can only be &p[0], and 0 must be connected in MST;							
	for (int i = 1; i != p.size(); ++i) { // p[0]=0;
		if (p[i] != i) {
			boost::add_edge(i, p[i], get(boost::edge_weight_t(), input_graph, boost::edge(i, p[i], input_graph).first), MST); // print edges (old costs)
		}
	}

	//cout << "here 1" << endl;

	//boost::property_map<graph, boost::edge_weight_t>::type EdgeWeightMap = get(boost::edge_weight_t(), MST);
	//typedef boost::graph_traits<graph>::edge_iterator edge_iter;
	//pair<edge_iter, edge_iter> edgePair;
	//for (edgePair = edges(MST); edgePair.first != edgePair.second; ++edgePair.first)
	//{
	//	cout << *edgePair.first << " "; // print edge
	//	cout << EdgeWeightMap[*edgePair.first] << endl; // print edge weight
	//}


	included_vertices.clear();
	for (int i = 0; i < N; i++) {
		included_vertices.insert(included_vertices.end(), i);  // update included_vertices
	}
	graph PostP_tree = group_pruning(input_graph, group_graph, MST, included_vertices);

	return PostP_tree;

	//cout << "here 2" << endl;

}
#pragma endregion MPA_NWFGSTP


#pragma region
template<class output_iterator>
void convert_number_to_array_of_digits(const unsigned number,
	output_iterator first, output_iterator last)
{
	const unsigned number_bits = CHAR_BIT * sizeof(int);
	//extract bits one at a time
	for (unsigned i = 0; i < number_bits && first != last; ++i) {
		const unsigned shift_amount = number_bits - i - 1;
		const unsigned this_bit = (number >> i) & 1;
		*first = this_bit;
		++first;
	}
	//pad the rest with zeros
	while (first != last) {
		*first = 0;
		++first;
	}
}
#pragma endregion convert_number_to_array_of_digits 2018年1月21日15:31:56


#pragma region
graph find_exact_solution_NWGSTP(graph input_graph, graph group_graph, std::vector<int>& included_vertices) {

	int V = num_vertices(input_graph);

	// find SMT; at least one vertex in min_binary
	double min_net_cost = 1e20;
	std::vector<int> min_included_vertices;
	graph GSMT;

	for (int Count_num = 0; Count_num < pow(2, V); Count_num++) {
		std::vector<int> binary(V);
		convert_number_to_array_of_digits(Count_num, std::begin(binary), std::end(binary));
		included_vertices.clear();
		for (int j = 0; j < V; j++) {
			if (binary[j] == 1) {
				included_vertices.insert(included_vertices.end(), j);
			}
		}

		if (solution_contain_all_groups(V, included_vertices, group_graph) == true) { // included_vertices contains all groups

			if (included_vertices.size() == 1) { // the SMT is a single vertex
				double net_cost1 = -get(boost::vertex_name_t(), input_graph, included_vertices[0]);
				if (net_cost1 < min_net_cost) {
					min_net_cost = net_cost1;
					min_included_vertices = copy_vector_int(included_vertices);
				}
			}
			else { // the SMT is the smaller MST
				std::vector<int> included(V);
				for (int j = 0; j < included_vertices.size(); j++) {
					included[included_vertices[j]] = 1;
				}
				graph temporary_graph = copy_graph(input_graph);
				for (int j = 0; j < V; j++) {
					if (included[j] == 0) {
						clear_vertex(j, temporary_graph);
					}
				}
				bool connected = true;
				std::vector<int> component(V); // vertex i is in component[i]; No.component from 0
				int cpn_num = connected_components(temporary_graph, &component[0]); // the number of component; decrease component
				int cpn_target;
				for (int i = 0; i < V; i++) {
					if (in_degree(i, temporary_graph) > 0) {
						cpn_target = component[i];
						break;
					}
				}
				for (int i = 0; i < V; i++) {
					if (in_degree(i, temporary_graph) > 0 && component[i] != cpn_target) {
						connected = false;
						break;
					}
				}
				if (connected == true) { // temporary_graph is connected

					MST_P3_Yahui_withoutTimeing(input_graph, temporary_graph); // find the MST
					double net_cost1 = net_cost(temporary_graph, included_vertices);
					if (net_cost1 < min_net_cost) {
						min_net_cost = net_cost1;
						min_included_vertices = copy_vector_int(included_vertices);
					}

				}

			}
		}

	}

	included_vertices = copy_vector_int(min_included_vertices);
	std::vector<int> included(V);
	for (int j = 0; j < included_vertices.size(); j++) {
		included[included_vertices[j]] = 1;
	}
	GSMT = copy_graph(input_graph);
	for (int j = 0; j < V; j++) {
		if (included[j] == 0) {
			clear_vertex(j, GSMT);
		}
	}
	MST_P3_Yahui_withoutTimeing(input_graph, GSMT); // find the MST
	return GSMT;

}
#pragma endregion find_exact_solution_NWGSTP


#pragma region
graph find_exact_solution_NWFGSTP(graph input_graph, graph group_graph, std::vector<int>& included_vertices, std::vector<int> LV) {

	int V = num_vertices(input_graph);

	// find SMT; at least one vertex in min_binary
	double min_net_cost = 1e20;
	std::vector<int> min_included_vertices;
	graph GSMT;

	for (int Count_num = 0; Count_num < pow(2, V); Count_num++) {
		std::vector<int> binary(V);
		convert_number_to_array_of_digits(Count_num, std::begin(binary), std::end(binary));
		included_vertices.clear();
		for (int j = 0; j < V; j++) {
			if (binary[j] == 1) {
				included_vertices.insert(included_vertices.end(), j);
			}
		}

		if (solution_contain_all_groups(V, included_vertices, group_graph) == true) { // included_vertices contains all groups

			if (included_vertices.size() == 1) { // the SMT is a single vertex
				double net_cost1 = -get(boost::vertex_name_t(), input_graph, included_vertices[0]);
				if (net_cost1 < min_net_cost) {
					min_net_cost = net_cost1;
					min_included_vertices = copy_vector_int(included_vertices);
				}
			}
			else { // the SMT is the smaller MST
				std::vector<int> included(V);
				for (int j = 0; j < included_vertices.size(); j++) {
					included[included_vertices[j]] = 1;
				}
				graph temporary_graph = copy_graph(input_graph);
				for (int j = 0; j < V; j++) {
					if (included[j] == 0) {
						clear_vertex(j, temporary_graph);
					}
				}
				bool connected = true;
				std::vector<int> component(V); // vertex i is in component[i]; No.component from 0
				int cpn_num = connected_components(temporary_graph, &component[0]); // the number of component; decrease component
				int cpn_target;
				for (int i = 0; i < V; i++) {
					if (in_degree(i, temporary_graph) > 0) {
						cpn_target = component[i];
						break;
					}
				}
				for (int i = 0; i < V; i++) {
					if (in_degree(i, temporary_graph) > 0 && component[i] != cpn_target) {
						connected = false;
						break;
					}
				}
				if (connected == true) { // temporary_graph is connected

					MFSTA(input_graph, temporary_graph, LV); // find the MST

					//cout << "here" << endl;
					double net_cost1 = net_cost(temporary_graph, included_vertices);
					if (net_cost1 < min_net_cost) {
						bool LV_feasible = true; // all LV are leaves in temporary_graph
						for (int i = 0; i < V; i++) {
							if (in_degree(i, temporary_graph) > 1 && LV[i] == 1) {
								LV_feasible = false;
								break;
							}
						}
						if (LV_feasible == true) {// feasible solution
							min_net_cost = net_cost1;
							min_included_vertices = copy_vector_int(included_vertices);
						}
					}
				}

			}
		}

	}

	included_vertices = copy_vector_int(min_included_vertices);
	std::vector<int> included(V);
	for (int j = 0; j < included_vertices.size(); j++) {
		included[included_vertices[j]] = 1;
	}
	GSMT = copy_graph(input_graph);
	for (int j = 0; j < V; j++) {
		if (included[j] == 0) {
			clear_vertex(j, GSMT);
		}
	}
	MFSTA(input_graph, GSMT, LV); // find the MST
	return GSMT;

}
#pragma endregion find_exact_solution_NWFGSTP


#pragma region
int count_connected_cpn_Vsize(graph input_graph, int StartVertex) {

	typedef boost::graph_traits<graph>::adjacency_iterator AdjacencyIterator;
	AdjacencyIterator ai, a_end;

	int V = num_vertices(input_graph);
	int cpn_size = 0;
	std::vector<int> touched(V);
	std::vector<int> added_to_be_touched(V); // it is necessary when input_graph is not a tree, otherwise to_be_touched may contain vertex repetitively
	std::vector<int> to_be_touched;

	touched[StartVertex] = 1;
	cpn_size++;

	boost::tie(ai, a_end) = boost::adjacent_vertices(StartVertex, input_graph);
	for (; ai != a_end; ai++) {
		added_to_be_touched[*ai] = 1;
		to_be_touched.insert(to_be_touched.end(), *ai);
	}

	while (to_be_touched.size() > 0) {
		touched[to_be_touched[0]] = 1;

		cpn_size++;
		boost::tie(ai, a_end) = boost::adjacent_vertices(to_be_touched[0], input_graph);
		for (; ai != a_end; ai++) {
			if (touched[*ai] == 0 && added_to_be_touched[*ai] == 0) {
				added_to_be_touched[*ai] = 1;
				to_be_touched.insert(to_be_touched.end(), *ai);
				//cout << "to_be_touched.insert " << *ai << endl;
			}
		}
		to_be_touched.erase(to_be_touched.begin());
	}

	return cpn_size;

}
#pragma endregion count_connected_cpn_Vsize 2018-5-17 14:31:43


#pragma region
graph find_exactCountCompulsory_solution_NWGSTP(graph input_graph, graph group_graph, std::vector<int>& included_vertices, int upperbound) {

	int V = num_vertices(input_graph);

	// find SMT; at least one vertex in min_binary
	double min_net_cost = 1e20;
	std::vector<int> min_included_vertices;
	graph GSMT;


	typedef boost::graph_traits<graph>::adjacency_iterator AdjacencyIterator;
	AdjacencyIterator ai, a_end;
	std::vector<int> CompulsoryVertex(V);
	int N_group = num_vertices(group_graph) - V;
	for (int i = 0; i < N_group; i++) {
		if (in_degree(i + V, group_graph) == 1) {
			boost::tie(ai, a_end) = boost::adjacent_vertices(i + V, group_graph);
			int vertex = *ai; // this group only contains this vertex
			CompulsoryVertex[vertex] = 1;
		}
	}
	std::vector<int> NonCompulsoryVertex;
	for (int i = 0; i < V; i++) {
		if (CompulsoryVertex[i] == 0) {
			NonCompulsoryVertex.insert(NonCompulsoryVertex.end(), i);
		}
	}
	int NonCompulsoryVertex_Num = NonCompulsoryVertex.size();

	if (NonCompulsoryVertex_Num > upperbound) { // it's too slow to keep calculating
		graph x(1);
		return x;
	}
	else {
		cout << NonCompulsoryVertex_Num << endl;
	}


	for (int count_num = 0; count_num < pow(2, NonCompulsoryVertex_Num); count_num++) {

		std::vector<int> binary(NonCompulsoryVertex_Num);
		convert_number_to_array_of_digits(count_num, std::begin(binary), std::end(binary));

		std::vector<int> IncludedVertex = copy_vector_int(CompulsoryVertex);
		for (int j = 0; j < NonCompulsoryVertex_Num; j++) {
			if (binary[j] == 1) {
				IncludedVertex[NonCompulsoryVertex[j]] = 1;
			}
		}
		included_vertices.clear();
		for (int j = 0; j < V; j++) {
			if (IncludedVertex[j] == 1) {
				included_vertices.insert(included_vertices.end(), j);
			}
		}

		if (solution_contain_all_groups(V, included_vertices, group_graph) == true) { // included_vertices contains all groups

			if (included_vertices.size() == 1) { // the SMT is a single vertex
				double net_cost1 = -get(boost::vertex_name_t(), input_graph, included_vertices[0]);
				if (net_cost1 < min_net_cost) {
					min_net_cost = net_cost1;
					min_included_vertices = copy_vector_int(included_vertices);
				}
			}
			else { // the SMT is the smaller MST

				graph temporary_graph = copy_graph(input_graph);
				for (int j = 0; j < V; j++) {
					if (IncludedVertex[j] == 0) {
						clear_vertex(j, temporary_graph); // temporary_graph only contain included parts
					}
				}

				int cpn_size = count_connected_cpn_Vsize(temporary_graph, included_vertices[0]);

				if (cpn_size == included_vertices.size()) { // temporary_graph is connected

					graph MST_graph = find_MST_Yahui_withoutTimeing(temporary_graph); // find the MST
					double net_cost1 = net_cost(MST_graph, included_vertices);

					if (net_cost1 < min_net_cost) {
						min_net_cost = net_cost1;
						min_included_vertices = copy_vector_int(included_vertices);
					}

				}

			}
		}

	}

	included_vertices = copy_vector_int(min_included_vertices);
	std::vector<int> included(V);
	for (int j = 0; j < included_vertices.size(); j++) {
		included[included_vertices[j]] = 1;
	}
	GSMT = copy_graph(input_graph);
	for (int j = 0; j < V; j++) {
		if (included[j] == 0) {
			clear_vertex(j, GSMT);
		}
	}
	GSMT = find_MST_Yahui_withoutTimeing(GSMT); // find the MST
	return GSMT;

}
#pragma endregion find_exactCountCompulsory_solution_NWGSTP


#pragma region
graph find_exactCountCompulsory_solution_NWFGSTP(graph input_graph, graph group_graph, std::vector<int>& included_vertices, std::vector<int> LV, int upperbound) {

	int V = num_vertices(input_graph);

	// find SMT; at least one vertex in min_binary
	double min_net_cost = 1e20;
	std::vector<int> min_included_vertices;
	graph GSMT;

	typedef boost::graph_traits<graph>::adjacency_iterator AdjacencyIterator;
	AdjacencyIterator ai, a_end;
	std::vector<int> CompulsoryVertex(V);
	int N_group = num_vertices(group_graph) - V;
	for (int i = 0; i < N_group; i++) {
		if (in_degree(i + V, group_graph) == 1) {
			boost::tie(ai, a_end) = boost::adjacent_vertices(i + V, group_graph);
			int vertex = *ai; // this group only contains this vertex
			CompulsoryVertex[vertex] = 1;
		}
	}
	std::vector<int> NonCompulsoryVertex;
	for (int i = 0; i < V; i++) {
		if (CompulsoryVertex[i] == 0) {
			NonCompulsoryVertex.insert(NonCompulsoryVertex.end(), i);
		}
	}
	int NonCompulsoryVertex_Num = NonCompulsoryVertex.size();

	if (NonCompulsoryVertex_Num > upperbound) { // it's too slow to keep calculating
		graph x(1);
		return x;
	}

	//cout << NonCompulsoryVertex_Num << " " << CompulsoryVertex[1] << endl;


	for (int count_num = 0; count_num < pow(2, NonCompulsoryVertex_Num); count_num++) {

		std::vector<int> binary(NonCompulsoryVertex_Num);
		convert_number_to_array_of_digits(count_num, std::begin(binary), std::end(binary));

		//for (int k = 0; k < binary.size(); k++) {
		//	cout << binary[k] << " " ;
		//}
		//cout << endl;
		//getchar();

		std::vector<int> IncludedVertex = copy_vector_int(CompulsoryVertex);
		for (int j = 0; j < NonCompulsoryVertex_Num; j++) {
			if (binary[j] == 1) {
				IncludedVertex[NonCompulsoryVertex[j]] = 1;
			}
		}
		included_vertices.clear();
		for (int j = 0; j < V; j++) {
			if (IncludedVertex[j] == 1) {
				included_vertices.insert(included_vertices.end(), j);
			}
		}

		if (solution_contain_all_groups(V, included_vertices, group_graph) == true) { // included_vertices contains all groups

			if (included_vertices.size() == 1) { // the SMT is a single vertex
				double net_cost1 = -get(boost::vertex_name_t(), input_graph, included_vertices[0]);
				if (net_cost1 < min_net_cost) {
					min_net_cost = net_cost1;
					min_included_vertices = copy_vector_int(included_vertices);
				}
			}
			else { // the SMT is the smaller MST
				std::vector<int> included(V);
				for (int j = 0; j < included_vertices.size(); j++) {
					included[included_vertices[j]] = 1;
				}
				graph temporary_graph = copy_graph(input_graph);
				for (int j = 0; j < V; j++) {
					if (included[j] == 0) {
						clear_vertex(j, temporary_graph);
					}
				}
				bool connected = true;
				std::vector<int> component(V); // vertex i is in component[i]; No.component from 0
				int cpn_num = connected_components(temporary_graph, &component[0]); // the number of component; decrease component
				int cpn_target;
				for (int i = 0; i < V; i++) {
					if (in_degree(i, temporary_graph) > 0) {
						cpn_target = component[i];
						break;
					}
				}
				for (int i = 0; i < V; i++) {
					if (in_degree(i, temporary_graph) > 0 && component[i] != cpn_target) {
						connected = false;
						break;
					}
				}
				if (connected == true) { // temporary_graph is connected

					MFSTA(input_graph, temporary_graph, LV); // find the MST

															 //cout << "here" << endl;
					double net_cost1 = net_cost(temporary_graph, included_vertices);
					if (net_cost1 < min_net_cost) {
						bool LV_feasible = true; // all LV are leaves in temporary_graph
						for (int i = 0; i < V; i++) {
							if (in_degree(i, temporary_graph) > 1 && LV[i] == 1) {
								LV_feasible = false;
								break;
							}
						}
						if (LV_feasible == true) {// feasible solution
							min_net_cost = net_cost1;
							min_included_vertices = copy_vector_int(included_vertices);
						}
					}
				}

			}
		}

	}

	included_vertices = copy_vector_int(min_included_vertices);
	std::vector<int> included(V);
	for (int j = 0; j < included_vertices.size(); j++) {
		included[included_vertices[j]] = 1;
	}
	GSMT = copy_graph(input_graph);
	for (int j = 0; j < V; j++) {
		if (included[j] == 0) {
			clear_vertex(j, GSMT);
		}
	}
	MFSTA(input_graph, GSMT, LV); // find the MST
	return GSMT;

}
#pragma endregion find_exactCountCompulsory_solution_NWFGSTP



#pragma region

graph FGW_Clustering_NWGSTP(graph input_graph, graph group_graph, std::vector<int>& included_vertices, double distribution_ratio) {

	double Global_time = 0; // global time
	int Active_C_num = 0; // the number of active clusters
	int N = num_vertices(input_graph); // number of vertices
	int ep_num = num_edges(input_graph) * 2; // total number of edge parts
	int ep_order = 0;
	node_min_heap node0;

	// Clusters: the number of clusters is always N
	graph C_containing_groups = copy_graph(group_graph); // i connects j+N means cluster i contains group j
	std::vector<bool> C_activity(N); // activity value of each C; false means inactive; initial value is false
	std::vector<double> C_event_time(N); // the event time for each C
	std::vector<double> C_deactivate_time(N); // the deactivate time for each C
	std::vector<std::vector<int>> C_V_list(N); // record the vertices in each C
	std::vector<pairing_heap<node_min_heap>> C_ep_PQ(N); // the PQ for edge parts in each C; node index: ep order in ep_list
	std::vector<int> V_locator(N); // the index of the maximal cluster containing the vertex
	// edge parts: PQ and their handles
	std::vector<int> ep_v1_list(ep_num); // class may be slow, so I seperate the ep_list
	std::vector<int> ep_v2_list(ep_num);
	std::vector<double> ep_EventTime_list(ep_num);
	std::vector<int> ep_ep2_order_list(ep_num);
	std::vector<handle_t_node_min_heap> handle_ep(ep_num); // store the handle for each edge part
	// the event PQ and their handles
	pairing_heap<node_min_heap> C_event_PQ; // PQ storing the event time of the active clusters; node index: cluster order
	std::vector<handle_t_node_min_heap> handle_Cevent(N);
	pairing_heap<node_min_heap> E_event_PQ; // PQ storing the active clusters; node index: cluster order
	std::vector<handle_t_node_min_heap> handle_Eevent(N);

	graph::out_edge_iterator eit, eend;

	// initialize the clusters
	for (int i = 0; i < N; i++)
	{
		C_V_list[i].insert(C_V_list[i].end(), i); // insert a vertex into the rear of C_V_list[i]
		V_locator[i] = i; // the maximal cluster containing vertex i
						  // add edge parts into C
		tie(eit, eend) = boost::out_edges(i, input_graph); // adjacent_vertices of i
		for_each(eit, eend,
			[&input_graph, &ep_v1_list, &ep_v2_list, &ep_ep2_order_list, &handle_ep, &C_ep_PQ, &node0, // the & above is the capture-list: the variables you can use inside
			&ep_order, &i, &ep_EventTime_list, &distribution_ratio](graph::edge_descriptor it) // for each adjacenct vertex boost::target(it, input_graph)
		{
			int j = boost::target(it, input_graph); // the adjacent vetex to i
			if (j > i) { // don't overcheck an edge
						 // the first ep
				ep_v1_list[ep_order] = i;
				ep_v2_list[ep_order] = j;
				ep_EventTime_list[ep_order] = get(boost::edge_weight_t(), input_graph, boost::edge(i, j, input_graph).first) / distribution_ratio; // halve the edge cost
				ep_ep2_order_list[ep_order] = ep_order + 1; // it points to the ep below
				node0.index = ep_order; // node index: ep order
				node0.priority_value = ep_EventTime_list[ep_order]; // priority: ep_EventTime
				handle_ep[ep_order] = C_ep_PQ[i].push(node0); // put this ep into cluster i
				ep_order++;
				// the second ep
				ep_v1_list[ep_order] = j;
				ep_v2_list[ep_order] = i;
				ep_EventTime_list[ep_order] = ep_EventTime_list[ep_order - 1] * (distribution_ratio - 1); // halve the edge cost
				ep_ep2_order_list[ep_order] = ep_order - 1; // it points to the ep above
				node0.index = ep_order; // node index: ep order
				node0.priority_value = ep_EventTime_list[ep_order]; // priority: ep_EventTime
				handle_ep[ep_order] = C_ep_PQ[j].push(node0); // put this ep into cluster j
				ep_order++;
			}
		});
		// for active cluster
		if (get(boost::vertex_name_t(), input_graph, i) > 0) {
			Active_C_num++; // the number of active clusters
			C_activity[i] = true; // this cluster is active
			C_event_time[i] = get(boost::vertex_name_t(), input_graph, i); // the event time is the node weight
																		   // push node into C_event_PQ
			node0.index = i; // node index: cluster order
			node0.priority_value = C_event_time[i]; // priority: node weight
			handle_Cevent[i] = C_event_PQ.push(node0); // into PQ
													   // all the ep for cluster i have been inserted into C_ep_PQ[i]; Note that, it's only true when i starts from 0 and j>i above
													   // push node into E_event_PQ
			node0.priority_value = C_ep_PQ[i].top().priority_value; // priority: the closest ep time
			handle_Eevent[i] = E_event_PQ.push(node0); // into PQ
		}
		else if (get(boost::vertex_name_t(), input_graph, i) < 0) {
			C_event_time[i] = get(boost::vertex_name_t(), input_graph, i); // the C_event_time is below 0 for negatively weighted nodes
		}
	}


	// FGW growth starts!
	graph output_graph(N); // the output graph
	for (int i = 0; i < N; i++) {
		double new_weight = get(boost::vertex_name_t(), input_graph, i);
		boost::put(boost::vertex_name_t(), output_graph, i, new_weight); // input node weights
	}
	int C0;
	int C1;
	int C2;
	int ep1;
	int ep2;
	double Tc;
	double Te;
	double r;
	double lowerbound = 1e-7;  // d is not used in this coding

	while (Active_C_num > 1) // stop the loop when there is only one active cluster left
	{
		// find the closest event
		Tc = C_event_PQ.top().priority_value; // this cluster event time
		Te = E_event_PQ.top().priority_value; // this edge event time

		if (Tc >= Te) { // edge event
			C1 = E_event_PQ.top().index; // the cluster C1 for this edge event
			ep1 = C_ep_PQ[C1].top().index; // the top ep in C1
			C2 = V_locator[ep_v2_list[ep1]]; // the cluster C2 for this edge event

			if (C1 == C2) { // the inside ep is triggered
				C_ep_PQ[C1].pop(); // pop out the inside ep
								   // decrease E_event_PQ for the change of event_C1
				node0.index = C1;
				node0.priority_value = C_ep_PQ[C1].top().priority_value; // theoretically C_ep_PQ[event_C1] should not be empty
				E_event_PQ.decrease(handle_Eevent[C1], node0);
			}
			else { // the outside ep is triggered
				Global_time = Te;
				ep2 = ep_ep2_order_list[ep1];

				if (C_activity[C2] == true) { // C2 is active
					r = ep_EventTime_list[ep2] - Global_time; // the slack of the responsible edge

					if (r > lowerbound) { // r is big; d is not used in this coding
										  // change two ep event time
						ep_EventTime_list[ep1] = Global_time + r / 2;
						ep_EventTime_list[ep2] = Global_time + r / 2;
						// update C_ep_PQ in C1
						node0.index = ep1;
						node0.priority_value = ep_EventTime_list[ep1];
						C_ep_PQ[C1].decrease(handle_ep[ep1], node0);
						// update C_ep_PQ in C2
						node0.index = ep2;
						node0.priority_value = ep_EventTime_list[ep2];
						C_ep_PQ[C2].increase(handle_ep[ep2], node0);
						// update E_event_PQ for the change of C1
						node0.index = C1;
						node0.priority_value = C_ep_PQ[C1].top().priority_value;
						E_event_PQ.decrease(handle_Eevent[C1], node0);
						// update E_event_PQ for the change of C2
						if (C_ep_PQ[C2].top().index == ep2) {
							node0.index = C2;
							node0.priority_value = C_ep_PQ[C2].top().priority_value;
							E_event_PQ.increase(handle_Eevent[C2], node0);
						}
					}
					else { // r is small; merge event
						   // add edge with the original cost
						boost::add_edge(ep_v1_list[ep1], ep_v1_list[ep2],
							get(boost::edge_weight_t(), input_graph,
								boost::edge(ep_v1_list[ep1], ep_v1_list[ep2], input_graph).first), output_graph);
						// merge V_list of C2 into C1
						C_V_list[C1].insert(end(C_V_list[C1]), begin(C_V_list[C2]), end(C_V_list[C2]));
						//decrease V_locator
						for (int i = 0; i < C_V_list[C2].size(); i++) {
							V_locator[C_V_list[C2][i]] = C1;
						}
						// update event time of C1
						C_event_time[C1] = C_event_time[C1] + C_event_time[C2] - Global_time;
						// minus one active cluster
						Active_C_num--;
						C_activity[C2] = false;
						C_deactivate_time[C2] = Global_time;
						// merge two C_ep_PQ
						C_ep_PQ[C1].pop(); // pop out the responsible ep
						C_ep_PQ[C1].merge(C_ep_PQ[C2]);
						// update C1 in C_event_time and E_event_time
						node0.index = C1;
						node0.priority_value = C_event_time[C1];
						C_event_PQ.decrease(handle_Cevent[C1], node0);
						node0.priority_value = C_ep_PQ[C1].top().priority_value;
						E_event_PQ.decrease(handle_Eevent[C1], node0);
						// remove C2 from C_event_time and E_event_time
						C_event_PQ.erase(handle_Cevent[C2]);
						E_event_PQ.erase(handle_Eevent[C2]);
					}
				}
				else { // C2 is inactive
					r = ep_EventTime_list[ep2] - C_deactivate_time[C2]; // the slack of the responsible edge

					if (r > lowerbound) { // r is big; d is not used in this coding
										  // change two ep event time
						ep_EventTime_list[ep1] = Global_time + r;
						ep_EventTime_list[ep2] = C_event_time[C2];
						// update C_ep_PQ in C1
						node0.index = ep1;
						node0.priority_value = ep_EventTime_list[ep1];
						C_ep_PQ[C1].decrease(handle_ep[ep1], node0);
						// update C_ep_PQ in C2
						node0.index = ep2;
						node0.priority_value = ep_EventTime_list[ep2];
						C_ep_PQ[C2].increase(handle_ep[ep2], node0);
						// update E_event_PQ for the change of C1
						node0.index = C1;
						node0.priority_value = C_ep_PQ[C1].top().priority_value;
						E_event_PQ.decrease(handle_Eevent[C1], node0);
					}
					else { // r is small; merge event
						   // add edge
						boost::add_edge(ep_v1_list[ep1], ep_v1_list[ep2],
							get(boost::edge_weight_t(), input_graph,
								boost::edge(ep_v1_list[ep1], ep_v1_list[ep2], input_graph).first), output_graph);
						// merge V_list of C2 into C1
						C_V_list[C1].insert(end(C_V_list[C1]), begin(C_V_list[C2]), end(C_V_list[C2]));
						//decrease V_locator
						for (int i = 0; i < C_V_list[C2].size(); i++) {
							V_locator[C_V_list[C2][i]] = C1;
						}
						// merge two C_ep_PQ
						C_ep_PQ[C1].pop(); // pop out the responsible ep		   
						typename pairing_heap<node_min_heap>::iterator begin = C_ep_PQ[C2].begin();
						typename pairing_heap<node_min_heap>::iterator end = C_ep_PQ[C2].end();
						for (typename pairing_heap<node_min_heap>::iterator it = begin; it != end; ++it)
						{
							node0 = *it;
							if (V_locator[ep_v2_list[node0.index]] != C1) { // only push outside nodes into C_ep_PQ[event_C1]; it's a little faster than not do that
								node0.priority_value = node0.priority_value + Global_time - C_event_time[C2]; // decrease priority values
								handle_ep[node0.index] = C_ep_PQ[C1].push(node0); // push; decrease handle
							}
						}

						// update event time of C1
						C_event_time[C1] = C_event_time[C1] - Global_time + C_event_time[C2] - C_deactivate_time[C2] + Global_time;
						if (C_event_time[C1] > Global_time) { // new C1 is active
															  // update C1 in C_event_time and E_event_time
							node0.index = C1;
							node0.priority_value = C_event_time[C1];
							C_event_PQ.decrease(handle_Cevent[C1], node0);
							node0.priority_value = C_ep_PQ[C1].top().priority_value;
							E_event_PQ.decrease(handle_Eevent[C1], node0);
						}
						else { // new C1 is inactive; deactivate C1
							Active_C_num--; // minus one active cluster
							C_event_PQ.erase(handle_Cevent[C1]);
							E_event_PQ.erase(handle_Eevent[C1]);
							C_activity[C1] = false; // deactivate it
							C_deactivate_time[C1] = Global_time;
						}
					}
				}
			}
		}
		else { // cluster event
			Global_time = Tc; // decrease time
			C0 = C_event_PQ.top().index; // the cluster for this cluster event
			Active_C_num--; // minus one active cluster
			C_event_PQ.pop(); // remove the cluster from C_event_PQ
			E_event_PQ.erase(handle_Eevent[C0]); // remove the cluster from E_event_PQ
			C_activity[C0] = false; // deactivate it
			C_deactivate_time[C0] = Global_time;
		}
	}

	// remove disconnected parts
	std::vector<int> component(N); // vertex i is in component[i]; No.component from 0
	int cpn_num = connected_components(output_graph, &component[0]); // the number of component; decrease component
	int R_cpn;
	if (C_event_PQ.size() == 0) {
		R_cpn = component[C_V_list[C1][0]]; // C1 is the last active cluster
	}
	else {
		R_cpn = component[C_V_list[C_event_PQ.top().index][0]]; // it throw exception when TP=0 and C_event_PQ.size()=0
	}
	for (int i = 0; i < N; i++) {
		if (component[i] != R_cpn && in_degree(i, output_graph) > 0) { // disconnected vertex
			clear_vertex(i, output_graph); // clear_vertex removes adjacent vertices, but not node weight
		}
	}

	return output_graph;

}
#pragma endregion FGW_Clustering_NWGSTP unfinished incomplete


#pragma region
void generate_random_NWGSTP_graphs_and_trees(int V, int E, int G, int V_tree, int g_size_min, int g_size_max,
	graph& random_graph, graph& group_graph, graph& spanning_tree) {

	typedef boost::graph_traits<graph>::adjacency_iterator AdjacencyIterator;
	AdjacencyIterator ai, a_end;
	typedef graph::edge_descriptor Edge;

	double ec_min = 1; // the min edge cost
	double ec_max = 10; // the max edge cost
	double nw_min = -10; // the min node weight
	double nw_max = -1; // the max node weight


	// generate random node weights to random_graph
	for (int i = 0; i < V; i++) {
		int new_weight = nw_min + (rand() % (int)(nw_max - nw_min + 1)); // generate int random number 
		boost::add_vertex(i, random_graph);
		boost::put(boost::vertex_name_t(), random_graph, i, new_weight); // put node weight
	}

	// add edges to random_graph
	if (E == V*(V - 1) / 2) { // complete graphs
		for (int i = 0; i < V; i++) {
			for (int j = 0; j < i; j++) {
				int new_cost = ec_min + (rand() % (int)(ec_max - ec_min + 1)); // generate int random number 
				boost::add_edge(i, j, new_cost, random_graph);
			}
		}
	}
	else { // incomplete graphs

		// generate a random spanning tree
		std::vector<int> inside_V; // the included vertex
		inside_V.insert(inside_V.end(), 0);
		while (inside_V.size() < V) {
			int v1 = rand() % inside_V.size();  // generate random number from [0, inside_V.size()-1]
			int v2 = inside_V.size();
			int new_cost = ec_min + (rand() % (int)(ec_max - ec_min + 1)); // generate int random number 
			boost::add_edge(v1, v2, new_cost, random_graph);
			inside_V.insert(inside_V.end(), v2);
		}

		std::vector<int> not_full_vertices; // vertices without a full degree
		for (int i = 0; i < V; i++) {
			not_full_vertices.insert(not_full_vertices.end(), i);
		}

		while (num_edges(random_graph) < E) {

			int RAND = 0 + (rand() % (int)(not_full_vertices.size() - 1 - 0 + 1)); // generate int random number  0, not_full_vertices.size()-1
			if (in_degree(not_full_vertices[RAND], random_graph) < V) { // this is a vertex without a full degree
				for (int i = 0; i < V; i++) {
					pair<Edge, bool> ed = boost::edge(not_full_vertices[RAND], i, random_graph);
					if (!ed.second && not_full_vertices[RAND] != i) { // This edge does not exist
						int new_cost = ec_min + (rand() % (int)(ec_max - ec_min + 1)); // generate int random number
						boost::add_edge(not_full_vertices[RAND], i, new_cost, random_graph); // add a new edge
						break; // break after adding one edge
					}
				}
			}
			else { // this is a vertex with a full degree
				not_full_vertices.erase(not_full_vertices.begin() + RAND);
			}

		}
	}

	// find MST
	spanning_tree = find_MST_Yahui_withoutTimeing(random_graph);
	// remove edges from MST
	int touched_ID = 0;
	std::vector<int> touched(V), included, to_be_touched, to_be_removed;
	touched[0] = 1;
	touched_ID = 1; // the first to_be_touched
	included.insert(included.end(), 0); // 0 is in the solution
	boost::tie(ai, a_end) = boost::adjacent_vertices(0, spanning_tree);
	for (; ai != a_end; ai++) {
		to_be_touched.insert(to_be_touched.end(), *ai);
	}
	for (int i = 0; i < to_be_touched.size(); i++) {
		boost::tie(ai, a_end) = boost::adjacent_vertices(to_be_touched[i], spanning_tree);
		touched[to_be_touched[i]] = 1;
		touched_ID++;
		if (touched_ID > V_tree) {
			to_be_removed.insert(to_be_removed.end(), to_be_touched[i]); // this vertex is to_be_removed
		}
		else {
			included.insert(included.end(), to_be_touched[i]); // to_be_touched[i] is in the solution
		}
		for (; ai != a_end; ai++) {
			if (touched[*ai] == 0) {
				to_be_touched.insert(to_be_touched.end(), *ai);
			}
		}
	}
	for (int i = 0; i < to_be_removed.size(); i++) {
		clear_vertex(to_be_removed[i], spanning_tree); // remove edges
	}


	// change edge costs in both random_graph and spanning_tree
	for (int i = 0; i < V; i++) {
		boost::tie(ai, a_end) = boost::adjacent_vertices(i, random_graph);
		for (; ai != a_end; ai++) {
			if (*ai > i) {
				int new_cost = ec_min + (rand() % (int)(ec_max - ec_min + 1)); // generate int random number
				pair<Edge, bool> ed = boost::edge(i, *ai, random_graph);
				boost::put(boost::edge_weight_t(), random_graph, ed.first, new_cost);
				ed = boost::edge(i, *ai, spanning_tree);
				if (ed.second) { // this edge is also in spanning_tree
					boost::put(boost::edge_weight_t(), spanning_tree, ed.first, new_cost);
				}
			}
		}
	}

	// add groups
	for (int i = 0; i < V; i++) {
		boost::add_vertex(i, group_graph);
	}
	while (num_vertices(group_graph) < V + G) {

		int group_centre = included[0 + (rand() % (int)(included.size() - 1 - 0 + 1))]; // group_centre is in the solution
		int group_size = g_size_min + (rand() % (int)(g_size_max - g_size_min + 1)); // generate int random number
		std::vector<int> group_vertices;
		std::vector<int> to_be_added;

		group_vertices.insert(group_vertices.end(), group_centre); // group_centre is the first group vertex
		boost::tie(ai, a_end) = boost::adjacent_vertices(group_centre, random_graph);
		for (; ai != a_end; ai++) {
			bool already_inside = false;
			for (int j = 0; j < group_vertices.size(); j++) {
				if (group_vertices[j] == *ai) {
					already_inside = true;
				}
			}
			if (already_inside == false) { // *ai is not in group_vertices
				to_be_added.insert(to_be_added.end(), *ai); // adjacent vertices of group_centre are to_be_added
			}
		}

		while (group_vertices.size() < group_size) { // find group_size vertices to generate a group
			group_vertices.insert(group_vertices.end(), to_be_added[0]); // add a new group vertex
			boost::tie(ai, a_end) = boost::adjacent_vertices(to_be_added[0], random_graph);
			for (; ai != a_end; ai++) {
				bool already_inside = false;
				for (int j = 0; j < group_vertices.size(); j++) {
					if (group_vertices[j] == *ai) {
						already_inside = true;
					}
				}
				if (already_inside == false) { // *ai is not in group_vertices
					to_be_added.insert(to_be_added.end(), *ai); // adjacent vertices of to_be_added[0] are to_be_added
				}
			}
			to_be_added.erase(to_be_added.begin());
		}

		// add this group
		int new_v = num_vertices(group_graph);
		boost::add_vertex(new_v, group_graph);
		for (int j = 0; j < group_vertices.size(); j++) {
			boost::add_edge(group_vertices[j], new_v, 1, group_graph);
		}


	}

}
#pragma endregion generate_random_NWGSTP_graphs_and_trees


#pragma region
void generate_random_NWGSTP_graphs(int V, int E, int G, int g_size_min, int g_size_max,
	graph& random_graph, graph& group_graph) {

	typedef boost::graph_traits<graph>::adjacency_iterator AdjacencyIterator;
	AdjacencyIterator ai, a_end;
	typedef graph::edge_descriptor Edge;

	double ec_min = 1; // the min edge cost
	double ec_max = 10; // the max edge cost
	double nw_min = -10; // the min node weight
	double nw_max = -1; // the max node weight


	// generate random node weights to random_graph
	for (int i = 0; i < V; i++) {
		int new_weight = nw_min + (rand() % (int)(nw_max - nw_min + 1)); // generate int random number 
		boost::add_vertex(i, random_graph);
		boost::put(boost::vertex_name_t(), random_graph, i, new_weight); // put node weight
	}

	// add edges to random_graph
	if (E == V*(V - 1) / 2) { // complete graphs
		for (int i = 0; i < V; i++) {
			for (int j = 0; j < i; j++) {
				int new_cost = ec_min + (rand() % (int)(ec_max - ec_min + 1)); // generate int random number 
				boost::add_edge(i, j, new_cost, random_graph);
			}
		}
	}
	else { // incomplete graphs

		   // generate a random spanning tree
		std::vector<int> inside_V; // the included vertex
		inside_V.insert(inside_V.end(), 0);
		while (inside_V.size() < V) {
			int v1 = rand() % inside_V.size();  // generate random number from [0, inside_V.size()-1]
			int v2 = inside_V.size();
			int new_cost = ec_min + (rand() % (int)(ec_max - ec_min + 1)); // generate int random number 
			boost::add_edge(v1, v2, new_cost, random_graph);
			inside_V.insert(inside_V.end(), v2);
		}

		std::vector<int> not_full_vertices; // vertices without a full degree
		for (int i = 0; i < V; i++) {
			not_full_vertices.insert(not_full_vertices.end(), i);
		}

		while (num_edges(random_graph) < E) {

			int RAND = 0 + (rand() % (int)(not_full_vertices.size() - 1 - 0 + 1)); // generate int random number  0, not_full_vertices.size()-1
			if (in_degree(not_full_vertices[RAND], random_graph) < V) { // this is a vertex without a full degree
				for (int i = 0; i < V; i++) {
					pair<Edge, bool> ed = boost::edge(not_full_vertices[RAND], i, random_graph);
					if (!ed.second && not_full_vertices[RAND] != i) { // This edge does not exist
						int new_cost = ec_min + (rand() % (int)(ec_max - ec_min + 1)); // generate int random number
						boost::add_edge(not_full_vertices[RAND], i, new_cost, random_graph); // add a new edge
						break; // break after adding one edge
					}
				}
			}
			else { // this is a vertex with a full degree
				not_full_vertices.erase(not_full_vertices.begin() + RAND);
			}

		}
	}

	// change edge costs in both random_graph and spanning_tree; there is actually no need to do this since the spanning tree is not the MST
	for (int i = 0; i < V; i++) {
		boost::tie(ai, a_end) = boost::adjacent_vertices(i, random_graph);
		for (; ai != a_end; ai++) {
			if (*ai > i) {
				int new_cost = ec_min + (rand() % (int)(ec_max - ec_min + 1)); // generate int random number
				pair<Edge, bool> ed = boost::edge(i, *ai, random_graph);
				boost::put(boost::edge_weight_t(), random_graph, ed.first, new_cost);
			}
		}
	}

	// add groups
	for (int i = 0; i < V; i++) {
		boost::add_vertex(i, group_graph);
	}
	while (num_vertices(group_graph) < V + G) {

		int group_centre = rand() % (int)V; // group_centre
		int group_size = g_size_min + (rand() % (int)(g_size_max - g_size_min + 1)); // generate int random number
		std::vector<int> group_vertices;
		std::vector<int> to_be_added;

		group_vertices.insert(group_vertices.end(), group_centre); // group_centre is the first group vertex
		boost::tie(ai, a_end) = boost::adjacent_vertices(group_centre, random_graph);
		for (; ai != a_end; ai++) {
			bool already_inside = false;
			for (int j = 0; j < group_vertices.size(); j++) {
				if (group_vertices[j] == *ai) {
					already_inside = true;
				}
			}
			if (already_inside == false) { // *ai is not in group_vertices; there is no need to do this! It's always false!
				to_be_added.insert(to_be_added.end(), *ai); // adjacent vertices of group_centre are to_be_added
			}
		}
		while (group_vertices.size() < group_size) { // find group_size vertices to generate a group
			int i = rand() % (int)to_be_added.size();
			group_vertices.insert(group_vertices.end(), to_be_added[i]); // add a new group vertex
			boost::tie(ai, a_end) = boost::adjacent_vertices(to_be_added[i], random_graph);
			for (; ai != a_end; ai++) {
				bool already_inside = false;
				for (int j = 0; j < group_vertices.size(); j++) {
					if (group_vertices[j] == *ai) {
						already_inside = true;
					}
				}
				if (already_inside == false) { // *ai is not in group_vertices
					to_be_added.insert(to_be_added.end(), *ai); // adjacent vertices of to_be_added[0] are to_be_added
				}
			}
			to_be_added.erase(to_be_added.begin() + i);
		}

		// add this group
		int new_v = num_vertices(group_graph);
		boost::add_vertex(new_v, group_graph);
		for (int j = 0; j < group_vertices.size(); j++) {
			boost::add_edge(group_vertices[j], new_v, 1, group_graph);
		}


	}

}
#pragma endregion generate_random_NWGSTP_graphs


#pragma region
void generate_random_NWFGSTP_graphs(int V, int E, int G, int S, int g_size_min, int g_size_max,
	graph& random_graph, graph& group_graph, std::vector<int>& LV) {

	typedef boost::graph_traits<graph>::adjacency_iterator AdjacencyIterator;
	AdjacencyIterator ai, a_end;
	typedef graph::edge_descriptor Edge;

	double ec_min = 1; // the min edge cost
	double ec_max = 10; // the max edge cost
	double nw_min = -10; // the min node weight
	double nw_max = -1; // the max node weight

	LV.resize(V);


	// generate random node weights to random_graph
	for (int i = 0; i < V; i++) {
		int new_weight = nw_min + (rand() % (int)(nw_max - nw_min + 1)); // generate int random number 
		boost::add_vertex(i, random_graph);
		boost::put(boost::vertex_name_t(), random_graph, i, new_weight); // put node weight
	}

	// add edges to random_graph
	if (E == V*(V - 1) / 2) { // complete graphs
		for (int i = 0; i < V; i++) {
			for (int j = 0; j < i; j++) {
				int new_cost = ec_min + (rand() % (int)(ec_max - ec_min + 1)); // generate int random number 
				boost::add_edge(i, j, new_cost, random_graph);
			}
		}
		for (int i = 0; i < S; i++) {
			LV[i] = 1;
		}
	}
	else { // incomplete graphs

		// generate a random spanning tree
		std::vector<int> inside_V; // the included vertex
		inside_V.insert(inside_V.end(), 0);
		if (S == V) {
			LV[0] = 1;
		}
		while (inside_V.size() < V - S) { // add non-LV
			int v1 = rand() % inside_V.size();  // generate random number from [0, inside_V.size()-1]
			int v2 = inside_V.size();
			int new_cost = ec_min + (rand() % (int)(ec_max - ec_min + 1)); // generate int random number 
			boost::add_edge(v1, v2, new_cost, random_graph);
			inside_V.insert(inside_V.end(), v2);
		}
		while (inside_V.size() < V) { // add LV; there is always a feasible solution
			int v1 = rand() % (V - S);  // generate random number from [0, V-S-1]
			int v2 = inside_V.size();
			int new_cost = ec_min + (rand() % (int)(ec_max - ec_min + 1)); // generate int random number 
			boost::add_edge(v1, v2, new_cost, random_graph); // v2 are leaf; sensors are always leaves
			inside_V.insert(inside_V.end(), v2);
			LV[v2] = 1;
		}

		std::vector<int> not_full_vertices; // vertices without a full degree
		for (int i = 0; i < V; i++) {
			not_full_vertices.insert(not_full_vertices.end(), i);
		}

		while (num_edges(random_graph) < E) {

			int RAND = 0 + (rand() % (int)(not_full_vertices.size() - 1 - 0 + 1)); // generate int random number  0, not_full_vertices.size()-1
			if (in_degree(not_full_vertices[RAND], random_graph) < V) { // this is a vertex without a full degree
				for (int i = 0; i < V; i++) {
					pair<Edge, bool> ed = boost::edge(not_full_vertices[RAND], i, random_graph);
					if (!ed.second && not_full_vertices[RAND] != i) { // This edge does not exist
						int new_cost = ec_min + (rand() % (int)(ec_max - ec_min + 1)); // generate int random number
						boost::add_edge(not_full_vertices[RAND], i, new_cost, random_graph); // add a new edge
						break; // break after adding one edge
					}
				}
			}
			else { // this is a vertex with a full degree
				not_full_vertices.erase(not_full_vertices.begin() + RAND);
			}

		}
	}

	// change edge costs in both random_graph and spanning_tree
	for (int i = 0; i < V; i++) {
		boost::tie(ai, a_end) = boost::adjacent_vertices(i, random_graph);
		for (; ai != a_end; ai++) {
			if (*ai > i) {
				int new_cost = ec_min + (rand() % (int)(ec_max - ec_min + 1)); // generate int random number
				pair<Edge, bool> ed = boost::edge(i, *ai, random_graph);
				boost::put(boost::edge_weight_t(), random_graph, ed.first, new_cost);
			}
		}
	}

	// add groups
	for (int i = 0; i < V; i++) {
		boost::add_vertex(i, group_graph);
	}
	while (num_vertices(group_graph) < V + G) {

		int group_centre = rand() % (int)V; // group_centre
		int group_size = g_size_min + (rand() % (int)(g_size_max - g_size_min + 1)); // generate int random number
		std::vector<int> group_vertices;
		std::vector<int> to_be_added;

		group_vertices.insert(group_vertices.end(), group_centre); // group_centre is the first group vertex
		boost::tie(ai, a_end) = boost::adjacent_vertices(group_centre, random_graph);
		for (; ai != a_end; ai++) {
			bool already_inside = false;
			for (int j = 0; j < group_vertices.size(); j++) {
				if (group_vertices[j] == *ai) {
					already_inside = true;
				}
			}
			if (already_inside == false) { // *ai is not in group_vertices
				to_be_added.insert(to_be_added.end(), *ai); // adjacent vertices of group_centre are to_be_added
			}
		}
		while (group_vertices.size() < group_size) { // find group_size vertices to generate a group
			int i = rand() % (int)to_be_added.size();
			group_vertices.insert(group_vertices.end(), to_be_added[i]); // add a new group vertex
			boost::tie(ai, a_end) = boost::adjacent_vertices(to_be_added[i], random_graph);
			for (; ai != a_end; ai++) {
				bool already_inside = false;
				for (int j = 0; j < group_vertices.size(); j++) {
					if (group_vertices[j] == *ai) {
						already_inside = true;
					}
				}
				if (already_inside == false) { // *ai is not in group_vertices
					to_be_added.insert(to_be_added.end(), *ai); // adjacent vertices of to_be_added[0] are to_be_added
				}
			}
			to_be_added.erase(to_be_added.begin() + i);
		}

		// add this group
		int new_v = num_vertices(group_graph);
		boost::add_vertex(new_v, group_graph);
		for (int j = 0; j < group_vertices.size(); j++) {
			boost::add_edge(group_vertices[j], new_v, 1, group_graph);
		}


	}

}
#pragma endregion generate_random_NWFGSTP_graphs


#pragma region
void NWGSTP_example() {

	graph g(52);

	boost::add_edge(0, 1, 5, g);
	//boost::add_edge(1, 2, 5, g);
	//boost::add_edge(0, 3, 7, g);
	//boost::add_edge(0, 4, 6, g);
	//boost::add_edge(2, 4, 7, g);
	//boost::add_edge(4, 5, 5, g);
	//boost::add_edge(5, 6, 5, g);
	//boost::add_edge(6, 7, 5, g);
	//boost::add_edge(7, 8, 5, g);

	//for (int i = 8; i < 5e1; i++) {
	//	boost::add_edge(i, i+1, 5, g);
	//}

	cout << "|V|=" << num_vertices(g) << " |E|=" << num_edges(g) << endl;

	boost::put(boost::vertex_name_t(), g, 0, -1);
	boost::put(boost::vertex_name_t(), g, 1, -2);
	//boost::put(boost::vertex_name_t(), g, 2, -2);
	//boost::put(boost::vertex_name_t(), g, 3, -2);
	//boost::put(boost::vertex_name_t(), g, 4, -2);
	//boost::put(boost::vertex_name_t(), g, 5, 0);

	int N = num_vertices(g);
	graph group_graph(N + 2); // groups
	boost::add_edge(N + 0, 0, 1, group_graph);
	boost::add_edge(N + 0, 1, 1, group_graph);
	boost::add_edge(N + 1, 1, 1, group_graph);
	//boost::add_edge(N + 1, 3, 1, group_graph); 
	//boost::add_edge(N + 1, 4, 1, group_graph);


	//save_NWGSTP_graph("Example", g, group_graph);

	// a solution
	graph solution = copy_graph(g);
	//boost::remove_edge(0, 3, solution);
	//boost::remove_edge(2, 4, solution);

	boost::property_map<graph, boost::edge_weight_t>::type EdgeWeightMap = get(boost::edge_weight_t(), solution);
	typedef boost::graph_traits<graph>::edge_iterator edge_iter;
	pair<edge_iter, edge_iter> edgePair;
	//for (edgePair = edges(solution); edgePair.first != edgePair.second; ++edgePair.first)
	//{
	//	cout << *edgePair.first << " "; // print edge
	//	cout << EdgeWeightMap[*edgePair.first] << endl; // print edge weight
	//}

	std::vector<int> included_vertices = find_included_vertices(g, group_graph, solution);

	//cout << "Feasible solution: " << solution_contain_all_groups(N, included_vertices, group_graph) << endl;
	cout << "Initial cost: " << net_cost(solution, included_vertices) << endl;



	auto begin = std::chrono::high_resolution_clock::now();

	//solution = leaf_replacing(g, group_graph, solution, included_vertices);
	solution = group_pruning(g, group_graph, solution, included_vertices);
	//solution = branch_replacing(g, group_graph, solution, included_vertices, 1);


	auto end = std::chrono::high_resolution_clock::now();
	float runningtime = std::chrono::duration_cast<std::chrono::nanoseconds>(end - begin).count(); // Nanosecond


	cout << "Feasible solution: " << solution_contain_all_groups(N, included_vertices, group_graph) << endl;
	cout << "Improved cost: " << net_cost(solution, included_vertices) << endl;
	std::cout << "Running time: " << runningtime / 1e6 << "ms" << std::endl;

	cout << "Included vertices:";
	for (int i = 0; i < included_vertices.size(); i++) {
		cout << " " << included_vertices[i];
	}
	cout << endl;


	for (edgePair = edges(solution); edgePair.first != edgePair.second; ++edgePair.first)
	{
		cout << *edgePair.first << " "; // print edge
		cout << EdgeWeightMap[*edgePair.first] << endl; // print edge weight
	}



	//// read graph
	//g.clear();
	//group_graph.clear();
	//g = read_NWGSTP_data("Example1.stp", group_graph);
	//int N_group = num_vertices(group_graph) - N;
	//cout << endl;
	//typedef boost::graph_traits<graph>::adjacency_iterator AdjacencyIterator;
	//AdjacencyIterator ai, a_end;
	//for (int i = 0; i < N_group; i++) {
	//	cout << "Group " << i << " contains vertices";
	//	boost::tie(ai, a_end) = boost::adjacent_vertices(i+N, group_graph);
	//	for (; ai != a_end; ai++) {
	//		int j = *ai; // group j-N
	//		cout << " " << j;
	//	}
	//	cout << endl;
	//}






}
#pragma endregion NWGSTP_example



#pragma region
graph PostP_GMLB(graph input_graph, graph group_graph, graph solution_graph, std::vector<int>& included_vertices, int alpha) {

	double initial_cost = net_cost(solution_graph, included_vertices);
	bool improved = true;
	graph PostP_tree = copy_graph(solution_graph);

	while (improved == true) {

		PostP_tree = group_pruning(input_graph, group_graph, PostP_tree, included_vertices);

		MST_P3_Yahui_withoutTimeing(input_graph, PostP_tree);

		PostP_tree = leaf_replacing(input_graph, group_graph, PostP_tree, included_vertices);

		PostP_tree = branch_replacing(input_graph, group_graph, PostP_tree, included_vertices, alpha);

		double new_cost = net_cost(PostP_tree, included_vertices);
		if (new_cost < initial_cost) {
			initial_cost = new_cost;
		}
		else {
			improved = false;
		}
	}

	return PostP_tree;

}
#pragma endregion PostP_GMLB


#pragma region
graph PostP_GMLB_NWFGSTP(graph input_graph, graph group_graph, graph solution_graph, std::vector<int>& included_vertices,
	int alpha, std::vector<int> LV) {

	double initial_cost = net_cost(solution_graph, included_vertices);
	bool improved = true;
	graph PostP_tree = copy_graph(solution_graph);

	while (improved == true) {

		PostP_tree = group_pruning(input_graph, group_graph, PostP_tree, included_vertices);

		MFSTA(input_graph, PostP_tree, LV);

		PostP_tree = leaf_replacing_NWFGSTP(input_graph, group_graph, PostP_tree, included_vertices, LV);

		PostP_tree = branch_replacing_NWFGSTP(input_graph, group_graph, PostP_tree, included_vertices, alpha, LV);

		double new_cost = net_cost(PostP_tree, included_vertices);
		if (new_cost < initial_cost) {
			initial_cost = new_cost;
		}
		else {
			improved = false;
		}
	}

	return PostP_tree;

}
#pragma endregion PostP_GMLB_NWFGSTP


#pragma region
graph PostP_GMG(graph input_graph, graph group_graph, graph solution_graph, std::vector<int>& included_vertices) {

	double initial_cost = net_cost(solution_graph, included_vertices);
	bool improved = true;
	graph PostP_tree = copy_graph(solution_graph);

	PostP_tree = group_pruning(input_graph, group_graph, PostP_tree, included_vertices); // it makes the MST technique below faster

	MST_P3_Yahui_withoutTimeing(input_graph, PostP_tree); // even though subnetworks of MST are also MST, but there 
	// may be multiple MSTs, and as a result, this MST technique may be triggered multiple times in iterations

	PostP_tree = group_pruning(input_graph, group_graph, PostP_tree, included_vertices);

	return PostP_tree;

}
#pragma endregion PostP_GMG


#pragma region
graph PostP_GMG_NWFGSTP(graph input_graph, graph group_graph, graph solution_graph, std::vector<int>& included_vertices, std::vector<int> LV) {

	double initial_cost = net_cost(solution_graph, included_vertices);
	bool improved = true;
	graph PostP_tree = copy_graph(solution_graph);

	PostP_tree = group_pruning(input_graph, group_graph, PostP_tree, included_vertices); // it makes the MST technique below faster

	MFSTA(input_graph, PostP_tree, LV); // even though subnetworks of MST are also MST, but there 
														  // may be multiple MSTs, and as a result, this MST technique may be triggered multiple times in iterations

	PostP_tree = group_pruning(input_graph, group_graph, PostP_tree, included_vertices);

	return PostP_tree;

}
#pragma endregion PostP_GMG_NWFGSTP


#pragma region
void random_graphs_PostP() {


	bool generate_new_graph = true;

	graph random_graph, group_graph, initial_tree, PostP_tree;

	if (generate_new_graph == true) {
		int V = 20, E = 50, G = 5, V_tree = 20;
		int g_size_min = 1;
		int g_size_max = 3;
		generate_random_NWGSTP_graphs_and_trees(V, E, G, V_tree, g_size_min, g_size_max, random_graph, group_graph, initial_tree);

		save_NWGSTP_graph("random_graph", random_graph, group_graph);
		save_NWGSTP_graph("spanning_tree", initial_tree, group_graph);
	}
	else {
		random_graph = read_NWGSTP_data("random_graph10.stp", group_graph);
		cout << endl;
		initial_tree = read_NWGSTP_data("spanning_tree10.stp", group_graph);
		cout << endl;
	}

	std::vector<int> included_vertices = find_included_vertices(random_graph, group_graph, initial_tree);
	cout << "Initial cost: " << net_cost(initial_tree, included_vertices) << endl;

	PostP_tree = PostP_GMG(random_graph, group_graph, initial_tree, included_vertices);

	cout << "Feasible solution: " << solution_contain_all_groups(num_vertices(random_graph), included_vertices, group_graph) << endl;
	cout << "Improved cost: " << net_cost(PostP_tree, included_vertices) << endl;

	cout << "Included vertices:";
	for (int i = 0; i < included_vertices.size(); i++) {
		cout << " " << included_vertices[i];
	}
	cout << endl;

	boost::property_map<graph, boost::edge_weight_t>::type EdgeWeightMap = get(boost::edge_weight_t(), PostP_tree);
	typedef boost::graph_traits<graph>::edge_iterator edge_iter;
	pair<edge_iter, edge_iter> edgePair;
	for (edgePair = edges(PostP_tree); edgePair.first != edgePair.second; ++edgePair.first)
	{
		cout << *edgePair.first << " "; // print edge
		cout << EdgeWeightMap[*edgePair.first] << endl; // print edge weight
	}









}
#pragma endregion random_graphs_PostP


#pragma region
graph PostP_GLB(graph input_graph, graph group_graph, graph solution_graph, std::vector<int>& included_vertices, int alpha) {

	double initial_cost = net_cost(solution_graph, included_vertices);
	bool improved = true;
	graph PostP_tree = copy_graph(solution_graph);

	while (improved == true) {

		PostP_tree = group_pruning(input_graph, group_graph, PostP_tree, included_vertices);

		//cout << "Included vertices 1:";
		//for (int i = 0; i < included_vertices.size(); i++) {
		//	cout << " " << included_vertices[i];
		//}
		//cout << endl;
		//boost::property_map<graph, boost::edge_weight_t>::type EdgeWeightMap = get(boost::edge_weight_t(), PostP_tree);
		//typedef boost::graph_traits<graph>::edge_iterator edge_iter;
		//pair<edge_iter, edge_iter> edgePair;
		//for (edgePair = edges(PostP_tree); edgePair.first != edgePair.second; ++edgePair.first)
		//{
		//	cout << *edgePair.first << " "; // print edge
		//	cout << EdgeWeightMap[*edgePair.first] << endl; // print edge weight
		//}


		PostP_tree = leaf_replacing(input_graph, group_graph, PostP_tree, included_vertices);

		//cout << "Included vertices 2:";
		//for (int i = 0; i < included_vertices.size(); i++) {
		//	cout << " " << included_vertices[i];
		//}
		//cout << endl;
		//EdgeWeightMap = get(boost::edge_weight_t(), PostP_tree);
		//for (edgePair = edges(PostP_tree); edgePair.first != edgePair.second; ++edgePair.first)
		//{
		//	cout << *edgePair.first << " "; // print edge
		//	cout << EdgeWeightMap[*edgePair.first] << endl; // print edge weight
		//}

		PostP_tree = branch_replacing(input_graph, group_graph, PostP_tree, included_vertices, alpha);

		//cout << "Included vertices 3:";
		//for (int i = 0; i < included_vertices.size(); i++) {
		//	cout << " " << included_vertices[i];
		//}
		//cout << endl;
		//EdgeWeightMap = get(boost::edge_weight_t(), PostP_tree);
		//for (edgePair = edges(PostP_tree); edgePair.first != edgePair.second; ++edgePair.first)
		//{
		//	cout << *edgePair.first << " "; // print edge
		//	cout << EdgeWeightMap[*edgePair.first] << endl; // print edge weight
		//}

		double new_cost = net_cost(PostP_tree, included_vertices);
		if (new_cost < initial_cost) {
			initial_cost = new_cost;
		}
		else {
			improved = false;
		}
	}

	return PostP_tree;

}
#pragma endregion PostP_GLB


#pragma region
graph PostP_GBL(graph input_graph, graph group_graph, graph solution_graph, std::vector<int>& included_vertices, int alpha) {

	double initial_cost = net_cost(solution_graph, included_vertices);
	bool improved = true;
	graph PostP_tree = copy_graph(solution_graph);

	while (improved == true) {

		PostP_tree = group_pruning(input_graph, group_graph, PostP_tree, included_vertices);
		PostP_tree = branch_replacing(input_graph, group_graph, PostP_tree, included_vertices, alpha);
		PostP_tree = leaf_replacing(input_graph, group_graph, PostP_tree, included_vertices);

		double new_cost = net_cost(PostP_tree, included_vertices);
		if (new_cost < initial_cost) {
			initial_cost = new_cost;
		}
		else {
			improved = false;
		}
	}

	return PostP_tree;

}
#pragma endregion PostP_GBL


#pragma region
graph PostP_LBG(graph input_graph, graph group_graph, graph solution_graph, std::vector<int>& included_vertices, int alpha) {

	double initial_cost = net_cost(solution_graph, included_vertices);
	bool improved = true;
	graph PostP_tree = copy_graph(solution_graph);

	while (improved == true) {


		PostP_tree = leaf_replacing(input_graph, group_graph, PostP_tree, included_vertices);


		PostP_tree = branch_replacing(input_graph, group_graph, PostP_tree, included_vertices, alpha);


		PostP_tree = group_pruning(input_graph, group_graph, PostP_tree, included_vertices);


		double new_cost = net_cost(PostP_tree, included_vertices);
		if (new_cost < initial_cost) {
			initial_cost = new_cost;
		}
		else {
			improved = false;
		}
	}

	return PostP_tree;

}
#pragma endregion PostP_LBG


#pragma region
graph PostP_LGB(graph input_graph, graph group_graph, graph solution_graph, std::vector<int>& included_vertices, int alpha) {

	double initial_cost = net_cost(solution_graph, included_vertices);
	bool improved = true;
	graph PostP_tree = copy_graph(solution_graph);

	while (improved == true) {

		PostP_tree = leaf_replacing(input_graph, group_graph, PostP_tree, included_vertices);
		PostP_tree = group_pruning(input_graph, group_graph, PostP_tree, included_vertices);
		PostP_tree = branch_replacing(input_graph, group_graph, PostP_tree, included_vertices, alpha);

		double new_cost = net_cost(PostP_tree, included_vertices);
		if (new_cost < initial_cost) {
			initial_cost = new_cost;
		}
		else {
			improved = false;
		}
	}

	return PostP_tree;

}
#pragma endregion PostP_LGB


#pragma region
graph PostP_BGL(graph input_graph, graph group_graph, graph solution_graph, std::vector<int>& included_vertices, int alpha) {

	double initial_cost = net_cost(solution_graph, included_vertices);
	bool improved = true;
	graph PostP_tree = copy_graph(solution_graph);

	while (improved == true) {

		PostP_tree = branch_replacing(input_graph, group_graph, PostP_tree, included_vertices, alpha);
		PostP_tree = group_pruning(input_graph, group_graph, PostP_tree, included_vertices);
		PostP_tree = leaf_replacing(input_graph, group_graph, PostP_tree, included_vertices);

		double new_cost = net_cost(PostP_tree, included_vertices);
		if (new_cost < initial_cost) {
			initial_cost = new_cost;
		}
		else {
			improved = false;
		}
	}

	return PostP_tree;

}
#pragma endregion PostP_BGL


#pragma region
graph PostP_BLG(graph input_graph, graph group_graph, graph solution_graph, std::vector<int>& included_vertices, int alpha) {

	double initial_cost = net_cost(solution_graph, included_vertices);
	bool improved = true;
	graph PostP_tree = copy_graph(solution_graph);

	while (improved == true) {

		PostP_tree = branch_replacing(input_graph, group_graph, PostP_tree, included_vertices, alpha);
		PostP_tree = leaf_replacing(input_graph, group_graph, PostP_tree, included_vertices);
		PostP_tree = group_pruning(input_graph, group_graph, PostP_tree, included_vertices);

		double new_cost = net_cost(PostP_tree, included_vertices);
		if (new_cost < initial_cost) {
			initial_cost = new_cost;
		}
		else {
			improved = false;
		}
	}

	return PostP_tree;

}
#pragma endregion PostP_BLG


#pragma region
void six_PostP_combinations() {

	bool generate_new_graph = false;

	graph random_graph, group_graph, initial_tree;

	if (generate_new_graph == true) {
		int V = 5, E = 10, G = 3, V_tree = 5;
		int g_size_min = 1;
		int g_size_max = 3;
		generate_random_NWGSTP_graphs_and_trees(V, E, G, V_tree, g_size_min, g_size_max, random_graph, group_graph, initial_tree);

		save_NWGSTP_graph("random_graph", random_graph, group_graph);
		save_NWGSTP_graph("spanning_tree", initial_tree, group_graph);
	}
	else {
		random_graph = read_NWGSTP_data("random_graph.stp", group_graph);
		cout << endl;
		initial_tree = read_NWGSTP_data("spanning_tree.stp", group_graph);
		cout << endl;
	}

	std::vector<int> Initial_included_vertices = find_included_vertices(random_graph, group_graph, initial_tree);
	if (solution_contain_all_groups(num_vertices(random_graph), Initial_included_vertices, group_graph) == false) {
		cout << "initial_tree is NOT feasible!" << endl;
	}
	connectivity_check_ignore_isolated_vertices(num_vertices(random_graph), initial_tree);
	cout << "Initial cost: " << net_cost(initial_tree, Initial_included_vertices) << endl;

	std::vector<int> exact_included_vertices;
	graph exact_solution = find_exact_solution_NWGSTP(random_graph, group_graph, exact_included_vertices);
	if (solution_contain_all_groups(num_vertices(random_graph), exact_included_vertices, group_graph) == false) {
		cout << "exact_solution is NOT feasible!" << endl;
	}
	connectivity_check_ignore_isolated_vertices(num_vertices(random_graph), exact_solution);
	cout << "exact_solution cost: " << net_cost(exact_solution, exact_included_vertices) << endl;
	//boost::property_map<graph, boost::edge_weight_t>::type EdgeWeightMap = get(boost::edge_weight_t(), exact_solution);
	//typedef boost::graph_traits<graph>::edge_iterator edge_iter;
	//pair<edge_iter, edge_iter> edgePair;
	//for (edgePair = edges(exact_solution); edgePair.first != edgePair.second; ++edgePair.first)
	//{
	//	cout << *edgePair.first << " "; // print edge
	//	cout << EdgeWeightMap[*edgePair.first] << endl; // print edge weight
	//}
	//cout << "Included vertices:";
	//for (int i = 0; i < exact_included_vertices.size(); i++) {
	//	cout << " " << exact_included_vertices[i];
	//}
	//cout << endl;

	std::vector<int> MPA_included_vertices;
	graph MPA_solution = MPA(random_graph, group_graph, MPA_included_vertices);
	if (solution_contain_all_groups(num_vertices(random_graph), MPA_included_vertices, group_graph) == false) {
		cout << "MPA_solution is NOT feasible!" << endl;
	}
	connectivity_check_ignore_isolated_vertices(num_vertices(random_graph), MPA_solution);
	cout << "MPA_solution cost: " << net_cost(MPA_solution, MPA_included_vertices) << endl;
	//EdgeWeightMap = get(boost::edge_weight_t(), MPA_solution);
	//for (edgePair = edges(MPA_solution); edgePair.first != edgePair.second; ++edgePair.first)
	//{
	//	cout << *edgePair.first << " "; // print edge
	//	cout << EdgeWeightMap[*edgePair.first] << endl; // print edge weight
	//}
	//cout << "Included vertices:";
	//for (int i = 0; i < MPA_included_vertices.size(); i++) {
	//	cout << " " << MPA_included_vertices[i];
	//}
	//cout << endl;

	// PostP_GLB
	if (1 > 0) {
		std::vector<int> GLB_included_vertices = copy_vector_int(Initial_included_vertices);
		graph PostP_tree_GLB = PostP_GLB(random_graph, group_graph, initial_tree, GLB_included_vertices, 10);
		if (solution_contain_all_groups(num_vertices(random_graph), GLB_included_vertices, group_graph) == false) {
			cout << "PostP_tree_GLB is NOT feasible!" << endl;
		}
		cout << "PostP_tree_GLB cost: " << net_cost(PostP_tree_GLB, GLB_included_vertices) << endl;
	}


	// PostP_GBL
	if (1 > 0) {
		std::vector<int> GBL_included_vertices = copy_vector_int(Initial_included_vertices);
		graph PostP_tree_GBL = PostP_GBL(random_graph, group_graph, initial_tree, GBL_included_vertices, 1);
		if (solution_contain_all_groups(num_vertices(random_graph), GBL_included_vertices, group_graph) == false) {
			cout << "PostP_tree_GBL is NOT feasible!" << endl;
		}
		cout << "PostP_tree_GBL cost: " << net_cost(PostP_tree_GBL, GBL_included_vertices) << endl;
	}


	// PostP_LBG
	if (1 > 0) {
		std::vector<int> LBG_included_vertices = copy_vector_int(Initial_included_vertices);
		graph PostP_tree_LBG = PostP_LBG(random_graph, group_graph, initial_tree, LBG_included_vertices, 1);
		if (solution_contain_all_groups(num_vertices(random_graph), LBG_included_vertices, group_graph) == false) {
			cout << "PostP_tree_LBG is NOT feasible!" << endl;
		}
		cout << "PostP_tree_LBG cost: " << net_cost(PostP_tree_LBG, LBG_included_vertices) << endl;
	}


	// PostP_LGB
	if (1 > 0) {
		std::vector<int> LGB_included_vertices = copy_vector_int(Initial_included_vertices);
		graph PostP_tree_LGB = PostP_LGB(random_graph, group_graph, initial_tree, LGB_included_vertices, 1);
		if (solution_contain_all_groups(num_vertices(random_graph), LGB_included_vertices, group_graph) == false) {
			cout << "PostP_tree_LGB is NOT feasible!" << endl;
		}
		cout << "PostP_tree_LGB cost: " << net_cost(PostP_tree_LGB, LGB_included_vertices) << endl;
	}


	// PostP_BGL
	if (1 > 0) {
		std::vector<int> BGL_included_vertices = copy_vector_int(Initial_included_vertices);
		graph PostP_tree_BGL = PostP_BGL(random_graph, group_graph, initial_tree, BGL_included_vertices, 1);
		if (solution_contain_all_groups(num_vertices(random_graph), BGL_included_vertices, group_graph) == false) {
			cout << "PostP_tree_BGL is NOT feasible!" << endl;
		}
		cout << "PostP_tree_BGL cost: " << net_cost(PostP_tree_BGL, BGL_included_vertices) << endl;
	}


	// PostP_BLG
	if (1 > 0) {
		std::vector<int> BLG_included_vertices = copy_vector_int(Initial_included_vertices);
		graph PostP_tree_BLG = PostP_BLG(random_graph, group_graph, initial_tree, BLG_included_vertices, 1);
		if (solution_contain_all_groups(num_vertices(random_graph), BLG_included_vertices, group_graph) == false) {
			cout << "PostP_tree_BLG is NOT feasible!" << endl;
		}
		cout << "PostP_tree_BLG cost: " << net_cost(PostP_tree_BLG, BLG_included_vertices) << endl;
	}



}
#pragma endregion six_PostP_combinations


#pragma region
void MPA_approximation_ratio() {


	int iteration_times = 100;
	int V = 20, E = 190, G = 40;
	string save_name = "MPA_approximation_ratio_V_" + to_string(V) + "_E_" + to_string(E) + "_G_" + to_string(G) + ".csv";
	int g_size_min = 1;
	int g_size_max = 2;
	double alpha = 1;

	ofstream outputFile;
	outputFile.precision(4);
	outputFile.setf(ios::fixed);
	outputFile.setf(ios::showpoint);
	outputFile.open(save_name);
	outputFile << "practice_approximation_ratio" << endl;

	int times = 0;
	while (times < iteration_times) {
		times++;

		graph random_graph, group_graph, initial_tree;
		generate_random_NWGSTP_graphs(V, E, G, g_size_min, g_size_max, random_graph, group_graph);

		std::vector<int> exact_included_vertices;
		auto begin = std::chrono::high_resolution_clock::now();
		graph exact_solution = find_exact_solution_NWGSTP(random_graph, group_graph, exact_included_vertices);
		auto end = std::chrono::high_resolution_clock::now();
		double exact_time = std::chrono::duration_cast<std::chrono::nanoseconds>(end - begin).count() / 1e6; // milliseconds
		cout << "Exact time: " << exact_time << "ms" << endl;
		//getchar();
		cout << "exact_solution cost: " << net_cost(exact_solution, exact_included_vertices) << endl;
		std::vector<int> MPA_included_vertices;
		graph MPA_solution = MPA(random_graph, group_graph, MPA_included_vertices);
		cout << "MPA_solution cost: " << net_cost(MPA_solution, MPA_included_vertices) << endl;
		double ratio1 = net_cost(MPA_solution, MPA_included_vertices) / net_cost(exact_solution, exact_included_vertices);

		std::vector<int> Post1_included_vertices = copy_vector_int(MPA_included_vertices);
		graph PostP_GMLB_solu = PostP_GMLB(random_graph, group_graph, MPA_solution, Post1_included_vertices, alpha);
		cout << "PostP_GMLB_solu cost: " << net_cost(PostP_GMLB_solu, Post1_included_vertices) << endl;
		double ratio2 = net_cost(PostP_GMLB_solu, Post1_included_vertices) / net_cost(exact_solution, exact_included_vertices);

		std::vector<int> Post2_included_vertices = copy_vector_int(MPA_included_vertices);
		graph PostP_GMG_solu = PostP_GMG(random_graph, group_graph, MPA_solution, Post2_included_vertices);
		cout << "PostP_GMG_solu cost: " << net_cost(PostP_GMG_solu, Post2_included_vertices) << endl;
		double ratio3 = net_cost(PostP_GMG_solu, Post2_included_vertices) / net_cost(exact_solution, exact_included_vertices);


		outputFile << ratio1 << "," << ratio2 << "," << ratio3 << endl;

	}


}
#pragma endregion MPA_approximation_ratio


#pragma region
void MPA_approximation_ratio_NWFGSTP() {


	int iteration_times = 100;
	int V = 10, E = 45, G = 20, S = 5;
	string save_name = "MPA_approximation_ratio_NWFGSTP_V_" + to_string(V) + "_E_" + to_string(E) + "_G_" + to_string(G) + ".csv";
	int g_size_min = 1;
	int g_size_max = 3;
	double alpha = 1;
	std::vector<int> LV;

	ofstream outputFile;
	outputFile.precision(4);
	outputFile.setf(ios::fixed);
	outputFile.setf(ios::showpoint);
	outputFile.open(save_name);
	outputFile << "practice_approximation_ratio" << endl;

	int times = 0;
	while (times < iteration_times) {
		times++;

		graph random_graph, group_graph, initial_tree;
		generate_random_NWFGSTP_graphs(V, E, G, S, g_size_min, g_size_max, random_graph, group_graph, LV);

		std::vector<int> exact_included_vertices;
		graph exact_solution = find_exact_solution_NWFGSTP(random_graph, group_graph, exact_included_vertices, LV);
		cout << "exact_solution cost: " << net_cost(exact_solution, exact_included_vertices) << endl;
		std::vector<int> MPA_included_vertices;
		graph MPA_solution = MPA_NWFGSTP(random_graph, group_graph, MPA_included_vertices, LV);
		cout << "MPA_solution cost: " << net_cost(MPA_solution, MPA_included_vertices) << endl;
		double ratio1 = net_cost(MPA_solution, MPA_included_vertices) / net_cost(exact_solution, exact_included_vertices);

		std::vector<int> Post1_included_vertices = copy_vector_int(MPA_included_vertices);
		graph PostP_GMLB_solu = PostP_GMLB_NWFGSTP(random_graph, group_graph, MPA_solution, Post1_included_vertices, alpha, LV);
		cout << "PostP_GMLB_solu cost: " << net_cost(PostP_GMLB_solu, Post1_included_vertices) << endl;
		double ratio2 = net_cost(PostP_GMLB_solu, Post1_included_vertices) / net_cost(exact_solution, exact_included_vertices);

		std::vector<int> Post2_included_vertices = copy_vector_int(MPA_included_vertices);
		graph PostP_GMG_solu = PostP_GMG_NWFGSTP(random_graph, group_graph, MPA_solution, Post2_included_vertices, LV);
		cout << "PostP_GMG_solu cost: " << net_cost(PostP_GMG_solu, Post2_included_vertices) << endl;
		double ratio3 = net_cost(PostP_GMG_solu, Post2_included_vertices) / net_cost(exact_solution, exact_included_vertices);


		outputFile << ratio1 << "," << ratio2 << "," << ratio3 << endl;

	}


}
#pragma endregion MPA_approximation_ratio_NWFGSTP


#pragma region
void MPA_approximation_ratio_Exact_CountCompulsory() {


	int iteration_times = 100;
	int V = 10, E = 45, G = 3;
	string save_name = "MPA_approximation_ratio_V_" + to_string(V) + "_E_" + to_string(E) + "_G_" + to_string(G) + ".csv";
	int g_size_min = 1;
	int g_size_max = 3;
	double alpha = 1;
	int upperbound = 20;

	ofstream outputFile;
	outputFile.precision(4);
	outputFile.setf(ios::fixed);
	outputFile.setf(ios::showpoint);
	outputFile.open(save_name);
	outputFile << "practice_approximation_ratio" << endl;

	int times = 0;
	while (times < iteration_times) {
		//times++;

		graph random_graph, group_graph, initial_tree;
		generate_random_NWGSTP_graphs(V, E, G, g_size_min, g_size_max, random_graph, group_graph);
		save_NWGSTP_graph("test", random_graph, group_graph);
		//random_graph = read_NWGSTP_data("test.stp", group_graph);

		std::vector<int> exact_included_vertices;
		auto begin = std::chrono::high_resolution_clock::now();
		cout << "here" << endl;
		graph exact_solution = find_exactCountCompulsory_solution_NWGSTP(random_graph, group_graph, exact_included_vertices, upperbound);
		auto end = std::chrono::high_resolution_clock::now();
		double exact_time = std::chrono::duration_cast<std::chrono::nanoseconds>(end - begin).count() / 1e6; // milliseconds
		cout << "Exact time: " << exact_time << "ms" << endl;
		//getchar();
		if (num_vertices(exact_solution) > 1) { // inside upperbound
			times++;
			
			cout << "exact_solution cost: " << net_cost(exact_solution, exact_included_vertices) << endl;
			std::vector<int> MPA_included_vertices;
			graph MPA_solution = MPA(random_graph, group_graph, MPA_included_vertices);
			cout << "MPA_solution cost: " << net_cost(MPA_solution, MPA_included_vertices) << endl;
			double ratio1 = net_cost(MPA_solution, MPA_included_vertices) / net_cost(exact_solution, exact_included_vertices);

			std::vector<int> Post1_included_vertices = copy_vector_int(MPA_included_vertices);
			graph PostP_GMLB_solu = PostP_GMLB(random_graph, group_graph, MPA_solution, Post1_included_vertices, alpha);
			cout << "PostP_GMLB_solu cost: " << net_cost(PostP_GMLB_solu, Post1_included_vertices) << endl;
			double ratio2 = net_cost(PostP_GMLB_solu, Post1_included_vertices) / net_cost(exact_solution, exact_included_vertices);

			std::vector<int> Post2_included_vertices = copy_vector_int(MPA_included_vertices);
			graph PostP_GMG_solu = PostP_GMG(random_graph, group_graph, MPA_solution, Post2_included_vertices);
			cout << "PostP_GMG_solu cost: " << net_cost(PostP_GMG_solu, Post2_included_vertices) << endl;
			double ratio3 = net_cost(PostP_GMG_solu, Post2_included_vertices) / net_cost(exact_solution, exact_included_vertices);

			if (ratio2 < 1 || ratio3 < 1) {
				cout << "Exact is not Exact!" << endl;
				getchar();
			}


			outputFile << ratio1 << "," << ratio2 << "," << ratio3 << endl;
		}


	}


}
#pragma endregion MPA_approximation_ratio_Exact_CountCompulsory


#pragma region
void MPA_approximation_ratio_NWFGSTP_Exact_CountCompulsory() {


	int iteration_times = 100;
	int V = 30, E = 435, G = 30, S = 10;
	string save_name = "MPA_approximation_ratio_NWFGSTP_V_" + to_string(V) + "_E_" + to_string(E) + "_G_" + to_string(G) + "_Exact_CountCompulsory.csv";
	int g_size_min = 1;
	int g_size_max = 3;
	double alpha = 1;
	std::vector<int> LV;
	int upperbound = 20;

	ofstream outputFile;
	outputFile.precision(4);
	outputFile.setf(ios::fixed);
	outputFile.setf(ios::showpoint);
	outputFile.open(save_name);
	outputFile << "practice_approximation_ratio" << endl;

	int times = 0;
	while (times < iteration_times) {
		//times++;

		graph random_graph, group_graph, initial_tree;
		generate_random_NWFGSTP_graphs(V, E, G, S, g_size_min, g_size_max, random_graph, group_graph, LV);
		

		std::vector<int> exact_included_vertices;
		graph exact_solution = find_exactCountCompulsory_solution_NWFGSTP(random_graph, group_graph, exact_included_vertices, LV, upperbound);
		cout << "exact_solution cost: " << net_cost(exact_solution, exact_included_vertices) << endl;

		if (num_vertices(exact_solution) > 1) { // inside upperbound
			times++;

			std::vector<int> MPA_included_vertices;
			graph MPA_solution = MPA_NWFGSTP(random_graph, group_graph, MPA_included_vertices, LV);
			cout << "MPA_solution cost: " << net_cost(MPA_solution, MPA_included_vertices) << endl;
			double ratio1 = net_cost(MPA_solution, MPA_included_vertices) / net_cost(exact_solution, exact_included_vertices);

			std::vector<int> Post1_included_vertices = copy_vector_int(MPA_included_vertices);
			graph PostP_GMLB_solu = PostP_GMLB_NWFGSTP(random_graph, group_graph, MPA_solution, Post1_included_vertices, alpha, LV);
			cout << "PostP_GMLB_solu cost: " << net_cost(PostP_GMLB_solu, Post1_included_vertices) << endl;
			double ratio2 = net_cost(PostP_GMLB_solu, Post1_included_vertices) / net_cost(exact_solution, exact_included_vertices);

			std::vector<int> Post2_included_vertices = copy_vector_int(MPA_included_vertices);
			graph PostP_GMG_solu = PostP_GMG_NWFGSTP(random_graph, group_graph, MPA_solution, Post2_included_vertices, LV);
			cout << "PostP_GMG_solu cost: " << net_cost(PostP_GMG_solu, Post2_included_vertices) << endl;
			double ratio3 = net_cost(PostP_GMG_solu, Post2_included_vertices) / net_cost(exact_solution, exact_included_vertices);


			outputFile << ratio1 << "," << ratio2 << "," << ratio3 << endl;
		}

		

	}


}
#pragma endregion MPA_approximation_ratio_NWFGSTP_Exact_CountCompulsory


#pragma region
void Compare_Exact_Count_notCount_Compulsory() {


	int iteration_times = 5;
	int V = 20, E = 190, G = 40;
	int g_size_min = 1;
	int g_size_max = 3;
	int upperbound = 20;


	int times = 0;
	double sum_time = 0;
	while (times < iteration_times) {
		

		graph random_graph, group_graph, initial_tree;
		generate_random_NWGSTP_graphs(V, E, G, g_size_min, g_size_max, random_graph, group_graph);

		//std::vector<int> exact_included_vertices;
		//auto begin = std::chrono::high_resolution_clock::now();
		//graph exact_solution = find_exact_solution_NWGSTP(random_graph, group_graph, exact_included_vertices);
		//auto end = std::chrono::high_resolution_clock::now();
		//double exact_time = std::chrono::duration_cast<std::chrono::nanoseconds>(end - begin).count() / 1e6; // milliseconds
		//cout << "Exact time: " << exact_time << "ms" << endl;
		//cout << "exact_solution cost: " << net_cost(exact_solution, exact_included_vertices) << endl;


		std::vector<int> exactCountCompulsory_included_vertices;
		auto begin = std::chrono::high_resolution_clock::now();
		graph exactCountCompulsory_solution = find_exactCountCompulsory_solution_NWGSTP(random_graph, group_graph, exactCountCompulsory_included_vertices,upperbound);
		auto end = std::chrono::high_resolution_clock::now();
		double exactCountCompulsory_time = std::chrono::duration_cast<std::chrono::nanoseconds>(end - begin).count() / 1e6; // milliseconds
		cout << "ExactCountCompulsory time: " << exactCountCompulsory_time << "ms" << endl;
		cout << "exactCountCompulsory_solution cost: " << net_cost(exactCountCompulsory_solution, exactCountCompulsory_included_vertices) << endl;


		if (num_vertices(exactCountCompulsory_solution) > 1) { // inside upperbound
			times++;
			sum_time = sum_time + exactCountCompulsory_time;
		}


		//getchar();


	}

	cout << "avg time: " << sum_time / iteration_times / 1e3 << "s" << endl;


}
#pragma endregion Compare_Exact_Count_notCount_Compulsory


#pragma region
void Compare_Exact_Count_notCount_Compulsory_NWFGSTP() {


	int iteration_times = 100;
	int V = 10, E = 45, G = 5, S = 5;
	int g_size_min = 1;
	int g_size_max = 3;
	int upperbound = 15;
	std::vector<int> LV;

	int times = 0;
	while (times < iteration_times) {
		times++;

		graph random_graph, group_graph;
		generate_random_NWFGSTP_graphs(V, E, G, S, g_size_min, g_size_max, random_graph, group_graph, LV);
		save_NWFGSTP_graph("example", random_graph, group_graph, LV);
		//random_graph = read_NWFGSTP_data("example.stp", group_graph, LV);

		std::vector<int> exact_included_vertices;
		auto begin = std::chrono::high_resolution_clock::now();
		graph exact_solution = find_exact_solution_NWFGSTP(random_graph, group_graph, exact_included_vertices, LV);
		auto end = std::chrono::high_resolution_clock::now();
		double exact_time = std::chrono::duration_cast<std::chrono::nanoseconds>(end - begin).count() / 1e6; // milliseconds
		cout << "Exact time: " << exact_time << "ms" << endl;
		cout << "exact_solution cost: " << net_cost(exact_solution, exact_included_vertices) << endl;

		//boost::property_map<graph, boost::edge_weight_t>::type EdgeWeightMap = get(boost::edge_weight_t(), exact_solution);
		//typedef boost::graph_traits<graph>::edge_iterator edge_iter;
		//pair<edge_iter, edge_iter> edgePair;
		//for (edgePair = edges(exact_solution); edgePair.first != edgePair.second; ++edgePair.first)
		//{
		//	cout << *edgePair.first << " "; // print edge
		//	cout << EdgeWeightMap[*edgePair.first] << endl; // print edge weight
		//}


		std::vector<int> exactCountCompulsory_included_vertices;
		begin = std::chrono::high_resolution_clock::now();
		graph exactCountCompulsory_solution = find_exactCountCompulsory_solution_NWFGSTP(random_graph, group_graph, exactCountCompulsory_included_vertices, LV, upperbound);
		end = std::chrono::high_resolution_clock::now();
		double exactCountCompulsory_time = std::chrono::duration_cast<std::chrono::nanoseconds>(end - begin).count() / 1e6; // milliseconds
		cout << "ExactCountCompulsory time: " << exactCountCompulsory_time << "ms" << endl;
		cout << "exactCountCompulsory_solution cost: " << net_cost(exactCountCompulsory_solution, exactCountCompulsory_included_vertices) << endl;

		//EdgeWeightMap = get(boost::edge_weight_t(), exactCountCompulsory_solution);
		//for (edgePair = edges(exactCountCompulsory_solution); edgePair.first != edgePair.second; ++edgePair.first)
		//{
		//	cout << *edgePair.first << " "; // print edge
		//	cout << EdgeWeightMap[*edgePair.first] << endl; // print edge weight
		//}

		getchar();

	}


}
#pragma endregion Compare_Exact_Count_notCount_Compulsory_NWFGSTP


#pragma region
void PostP_alpha_effect() {


	int iteration_times = 10;
	int V = 100, E = 450, G = 50;
	string save_name = "PostP_alpha_effect_V_" + to_string(V) + "_E_" + to_string(E) + "_G_" + to_string(G) + ".csv";
	int g_size_min = 1;
	int g_size_max = 2;

	ofstream outputFile;
	outputFile.precision(4);
	outputFile.setf(ios::fixed);
	outputFile.setf(ios::showpoint);
	outputFile.open(save_name);


	int times = 0;
	std::vector<double> runningtime_alpha(4); // alpha = 0, 1, 2, 3
	std::vector<double> Improve_ratio_alpha(4); // alpha = 0, 1, 2, 3
	while (times < iteration_times) {
		times++;
		cout << times << endl;

		graph random_graph, group_graph, initial_tree;
		generate_random_NWGSTP_graphs(V, E, G, g_size_min, g_size_max, random_graph, group_graph);
		std::vector<int> MPA_included_vertices;
		graph MPA_solution = MPA(random_graph, group_graph, MPA_included_vertices);
		cout << "MPA_solution cost: " << net_cost(MPA_solution, MPA_included_vertices) << endl;

		for (int alpha = 0; alpha < 4; alpha++) {
			std::vector<int> Post1_included_vertices = copy_vector_int(MPA_included_vertices);
			auto begin = std::chrono::high_resolution_clock::now();
			graph PostP_GMLB_solu = PostP_GMLB(random_graph, group_graph, MPA_solution, Post1_included_vertices, alpha);
			auto end = std::chrono::high_resolution_clock::now();
			double P_time = std::chrono::duration_cast<std::chrono::nanoseconds>(end - begin).count() / 1e6; // milliseconds
			double Improve_ratio = (net_cost(MPA_solution, MPA_included_vertices) - net_cost(PostP_GMLB_solu, Post1_included_vertices))
				/ net_cost(PostP_GMLB_solu, Post1_included_vertices);
			runningtime_alpha[alpha] = runningtime_alpha[alpha] + P_time;
			Improve_ratio_alpha[alpha] = Improve_ratio_alpha[alpha] + Improve_ratio;
		}

	}

	outputFile << "alpha,0,1,2,3" << endl;
	outputFile << "PostP time," << runningtime_alpha[0] / iteration_times<< "," << runningtime_alpha[1] / iteration_times << "," << 
		runningtime_alpha[2] / iteration_times << "," << runningtime_alpha[3] / iteration_times << "," << endl;
	outputFile << "PostP ratio," << Improve_ratio_alpha[0] / iteration_times << "," << Improve_ratio_alpha[1] / iteration_times << "," <<
		Improve_ratio_alpha[2] / iteration_times << "," << Improve_ratio_alpha[3] / iteration_times << "," << endl;


}
#pragma endregion PostP_alpha_effect


#pragma region
void twentyfour_PostP_combinations_compare() {

	int iteration_times = 100;
	int alpha = 2;

	graph random_graph, group_graph, initial_tree;
	int V = 100, E = 1000, G = 10, V_tree = 50;
	int g_size_min = 1;
	int g_size_max = 5;
	generate_random_NWGSTP_graphs_and_trees(V, E, G, V_tree, g_size_min, g_size_max, random_graph, group_graph, initial_tree);
	std::vector<int> Initial_included_vertices = find_included_vertices(random_graph, group_graph, initial_tree);
	if (solution_contain_all_groups(num_vertices(random_graph), Initial_included_vertices, group_graph) == false) {
		cout << "initial_tree is NOT feasible!" << endl;
		getchar();
	}
	connectivity_check_ignore_isolated_vertices(num_vertices(random_graph), initial_tree);


	std::vector<std::vector<string>> implementation_order;
	implementation_order.insert(implementation_order.end(), { "G","L","B","M" });
	implementation_order.insert(implementation_order.end(), { "G","B","L","M" });
	implementation_order.insert(implementation_order.end(), { "L","G","B","M" });
	implementation_order.insert(implementation_order.end(), { "L","B","G","M" });
	implementation_order.insert(implementation_order.end(), { "B","G","L","M" });
	implementation_order.insert(implementation_order.end(), { "B","L","G","M" });

	implementation_order.insert(implementation_order.end(), { "G","L","M","B" });
	implementation_order.insert(implementation_order.end(), { "G","B","M","L" });
	implementation_order.insert(implementation_order.end(), { "L","G","M","B" });
	implementation_order.insert(implementation_order.end(), { "L","B","M","G" });
	implementation_order.insert(implementation_order.end(), { "B","G","M","L" });
	implementation_order.insert(implementation_order.end(), { "B","L","M","G" });

	implementation_order.insert(implementation_order.end(), { "G","M","L","B" });
	implementation_order.insert(implementation_order.end(), { "G","M","B","L" });
	implementation_order.insert(implementation_order.end(), { "L","M","G","B" });
	implementation_order.insert(implementation_order.end(), { "L","M","B","G" });
	implementation_order.insert(implementation_order.end(), { "B","M","G","L" });
	implementation_order.insert(implementation_order.end(), { "B","M","L","G" });

	implementation_order.insert(implementation_order.end(), { "M","G","L","B" });
	implementation_order.insert(implementation_order.end(), { "M","G","B","L" });
	implementation_order.insert(implementation_order.end(), { "M","L","G","B" });
	implementation_order.insert(implementation_order.end(), { "M","L","B","G" });
	implementation_order.insert(implementation_order.end(), { "M","B","G","L" });
	implementation_order.insert(implementation_order.end(), { "M","B","L","G" });

	int times = 0;
	double new_cost, min_time, min_solution;
	bool improved;
	std::vector<int> included_vertices;
	std::vector<double> time(24);
	std::vector<double> cost(24);
	std::vector<int> solution_win_times(24);
	std::vector<int> speed_win_times(24);
	std::vector<double> average_solution(24);
	std::vector<double> average_speed(24);
	std::vector<string> order;
	graph PostP_tree;
	while (times < iteration_times) {
		times++;

		cout << "Times: " << times << endl;

		for (int x = 0; x < implementation_order.size(); x++) {

			order = copy_vector_string(implementation_order[x]);
			cost[x] = net_cost(initial_tree, included_vertices);
			included_vertices = copy_vector_int(Initial_included_vertices);
			improved = true;
			PostP_tree = copy_graph(initial_tree);
			auto begin = std::chrono::high_resolution_clock::now();
			while (improved == true) {
				for (int i = 0; i < 4; i++) {
					if (!order[i].compare("G")) {
						PostP_tree = group_pruning(random_graph, group_graph, PostP_tree, included_vertices);
					}
					else if (!order[i].compare("L")) {
						PostP_tree = leaf_replacing(random_graph, group_graph, PostP_tree, included_vertices);
					}
					else if (!order[i].compare("B")) {
						PostP_tree = branch_replacing(random_graph, group_graph, PostP_tree, included_vertices, alpha);
					}
					else if (!order[i].compare("M")) {
						MST_P3_Yahui_withoutTimeing(random_graph, PostP_tree);
					}
				}
				new_cost = net_cost(PostP_tree, included_vertices);
				if (new_cost < cost[x]) {
					cost[x] = new_cost;
				}
				else {
					improved = false;
				}
			}
			auto end = std::chrono::high_resolution_clock::now();
			time[x] = std::chrono::duration_cast<std::chrono::nanoseconds>(end - begin).count() / 1e6; // milliseconds
			if (solution_contain_all_groups(num_vertices(random_graph), included_vertices, group_graph) == false) {
				cout << "PostP_tree is NOT feasible!" << endl;
				getchar();
			}
		}


		// averae time/solution
		for (int x = 0; x < implementation_order.size(); x++) {
			average_speed[x] = average_speed[x] + time[x] / iteration_times;
			average_solution[x] = average_solution[x] + cost[x] / iteration_times;
		}

		min_time = 1e10;
		min_solution = 1e10;
		for (int x = 0; x < implementation_order.size(); x++) {
			if (time[x] < min_time) {
				min_time = time[x];
			}
			if (cost[x] < min_solution) {
				min_solution = cost[x];
			}
		}
		for (int x = 0; x < implementation_order.size(); x++) {
			if (time[x] == min_time) {
				speed_win_times[x]++;
			}
			if (cost[x] == min_solution) {
				solution_win_times[x]++;
			}
		}

	}


	ofstream outputFile;
	outputFile.precision(4);
	outputFile.setf(ios::fixed);
	outputFile.setf(ios::showpoint);
	outputFile.open("twentyfour_PostP_combinations_compare.csv");
	outputFile << "V=" << V << ",E=" << E << ",G=" << G << ",V_tree=" << V_tree << ",alpha=" << alpha << endl;
	outputFile << ",solution_win_times,speed_win_times,average_solution,average_speed" << endl;
	for (int x = 0; x < implementation_order.size(); x++) {
		outputFile << implementation_order[x][0] + implementation_order[x][1] + implementation_order[x][2] + implementation_order[x][3] << ",";
		outputFile << solution_win_times[x] << "," << speed_win_times[x] << "," << average_solution[x] << "," << average_speed[x] << endl;
	}
	outputFile << endl;


}
#pragma endregion twentyfour_PostP_combinations_compare


#pragma region
void MPA_benhmark_test() {

	int V = 1000000, E = 5000000, G = 1000;
	int g_size_min = 1;
	int g_size_max = 3;
	double alpha = 50;

	graph random_graph, group_graph, initial_tree;

	auto begin = std::chrono::high_resolution_clock::now();
	generate_random_NWGSTP_graphs(V, E, G, g_size_min, g_size_max, random_graph, group_graph);
	auto end = std::chrono::high_resolution_clock::now();
	double time = std::chrono::duration_cast<std::chrono::nanoseconds>(end - begin).count() / 1e6; // milliseconds
	cout << "Graph_generation time: " << time << "ms" << endl;

	//random_graph = read_NWGSTP_data("S11.stp", group_graph);

	std::vector<int> MPA_included_vertices;
	begin = std::chrono::high_resolution_clock::now();
	graph MPA_solution = MPA(random_graph, group_graph, MPA_included_vertices);
	end = std::chrono::high_resolution_clock::now();
	time = std::chrono::duration_cast<std::chrono::nanoseconds>(end - begin).count() / 1e6; // milliseconds
	cout << "MPA_solution cost: " << net_cost(MPA_solution, MPA_included_vertices) << endl;
	cout << "MPA_solution time: " << time << "ms" << endl;

	begin = std::chrono::high_resolution_clock::now();
	//graph PostP_GMLB_solu = PostP_GMLB(random_graph, group_graph, MPA_solution, MPA_included_vertices, alpha);
	graph PostP_GMLB_solu = PostP_GMG(random_graph, group_graph, MPA_solution, MPA_included_vertices);
	end = std::chrono::high_resolution_clock::now();
	time = std::chrono::duration_cast<std::chrono::nanoseconds>(end - begin).count() / 1e6; // milliseconds
	cout << "PostP_GMLB_solu cost: " << net_cost(PostP_GMLB_solu, MPA_included_vertices) << endl;
	cout << "PostP_GMLB_solu time: " << time << "ms" << endl;





}
#pragma endregion MPA_benhmark_test


#pragma region
void generate_S_L() {

	int generate_numbers = 40;
	int g_size_min = 1;
	int g_size_max = 3;

	for (int i = 1; i <= generate_numbers; i++) {

		string name;
		int V, E, G;

		if (i <= 20) {
			name = "S" + to_string(i);
			V = 1000;
			E = 10000;
			if (i <= 10) {
				G = 100;
			}
			else {
				G = 1000;
			}
		}
		else {
			name = "L" + to_string(i - 20);
			V = 100000;
			E = 1000000;
			if (i <= 30) {
				G = 1000;
			}
			else {
				G = 100000;
			}
		}

		graph random_graph, group_graph;
		generate_random_NWGSTP_graphs(V, E, G, g_size_min, g_size_max, random_graph, group_graph);
		save_NWGSTP_graph(name, random_graph, group_graph);


	}



}
#pragma endregion generate_S_L


#pragma region
void MPA_solve_S_L() {

	ofstream outputFile;
	outputFile.precision(2);
	outputFile.setf(ios::fixed);
	outputFile.setf(ios::showpoint);
	outputFile.open("MPA_S_L_results.csv");
	outputFile << "Instance,|V|,|E|,|G|,Solution,Time,Solution,Time" << endl;


	int generate_numbers = 40;
	int alpha = 3;
	graph random_graph, group_graph;

	for (int i = 1; i <= generate_numbers; i++) {

		string name;
		if (i <= 20) {
			name = "S" + to_string(i);
		}
		else {
			name = "L" + to_string(i - 20);
		}
		cout << name << " ";

		random_graph = read_NWGSTP_data(name + ".stp", group_graph);

		outputFile << name << "," << num_vertices(random_graph) << "," << num_edges(random_graph) << "," <<
			num_vertices(group_graph) - num_vertices(random_graph) << ",";

		std::vector<int> MPA_included_vertices;
		auto begin = std::chrono::high_resolution_clock::now();
		graph MPA_solution = MPA(random_graph, group_graph, MPA_included_vertices);
		auto end = std::chrono::high_resolution_clock::now();
		double MPA_time = std::chrono::duration_cast<std::chrono::nanoseconds>(end - begin).count() / 1e6; // milliseconds
		outputFile << net_cost(MPA_solution, MPA_included_vertices) << "," << MPA_time / 1e3 << "s,";

		begin = std::chrono::high_resolution_clock::now();
		graph PostP_GMLB_solu;
		if (i <= 10) {
			PostP_GMLB_solu = PostP_GMLB(random_graph, group_graph, MPA_solution, MPA_included_vertices, alpha);
		}
		else {
			PostP_GMLB_solu = PostP_GMG(random_graph, group_graph, MPA_solution, MPA_included_vertices);
		}
		end = std::chrono::high_resolution_clock::now();
		double PostP_time = std::chrono::duration_cast<std::chrono::nanoseconds>(end - begin).count() / 1e6; // milliseconds
		outputFile << net_cost(PostP_GMLB_solu, MPA_included_vertices) << "," << PostP_time / 1e3 << "s" << endl;
		cout << endl;
	}




}
#pragma endregion MPA_solve_S_L


#pragma region
void generate_T_benchmarks() {

	int generate_numbers = 20;
	int g_size_min = 1;
	int g_size_max = 3;

	for (int i = 1; i <= generate_numbers; i++) {

		string name = "T" + to_string(i);
		int V, E, G, S;
		std::vector<int> LV;

		if (i <= 10) {
			V = 1000;
			E = 10000;
			G = 100;
			S = 100;
		}
		else {
			V = 100000;
			E = 1000000;
			G = 100000;
			S = 10000;
		}

		graph random_graph, group_graph;
		generate_random_NWFGSTP_graphs(V, E, G, S, g_size_min, g_size_max, random_graph, group_graph, LV);
		save_NWFGSTP_graph(name, random_graph, group_graph, LV);


	}



}
#pragma endregion generate_T_benchmarks


#pragma region
bool LV_condition_met(graph solu_graph, std::vector<int> LV) {

	bool met = true;

	int N = num_vertices(solu_graph);
	for (int i = 0; i < N; i++) {
		if (in_degree(i, solu_graph) > 1 && LV[i] == 1) {
			met = false;
			break;
		}
	}

	return met;
}
#pragma endregion LV_condition_met


#pragma region
void MPA_solve_S_T() {

	ofstream outputFile;
	outputFile.precision(2);
	outputFile.setf(ios::fixed);
	outputFile.setf(ios::showpoint);
	outputFile.open("MPA_S_T_results.csv");
	outputFile << "Instance,|V|,|E|,|G|,|L|,Solution,Time,Solution,Time" << endl;


	int generate_numbers = 40;
	int alpha = 1;
	graph random_graph, group_graph;
	std::vector<int> LV;

	for (int i = 1; i <= generate_numbers; i++) {

		string name;
		if (i <= 20) {
			name = "S" + to_string(i);
			cout << name << " ";
			random_graph = read_NWGSTP_data(name + ".stp", group_graph);
		}
		else {
			name = "T" + to_string(i - 20);
			cout << name << " ";
			random_graph = read_NWFGSTP_data(name + ".stp", group_graph, LV);
		}

		int L_num = 0;
		for (int j = 0; j < LV.size(); j++) {
			if (LV[j] == 1) {
				L_num++;
			}
		}

		outputFile << name << "," << num_vertices(random_graph) << "," << num_edges(random_graph) << "," <<
			num_vertices(group_graph) - num_vertices(random_graph) << "," << L_num <<",";

		std::vector<int> MPA_included_vertices;
		auto begin = std::chrono::high_resolution_clock::now();
		graph MPA_solution;
		if (i <= 20) {
			MPA_solution = MPA(random_graph, group_graph, MPA_included_vertices);
		}
		else {
			MPA_solution = MPA_NWFGSTP(random_graph, group_graph, MPA_included_vertices, LV);
		}
		auto end = std::chrono::high_resolution_clock::now();
		double MPA_time = std::chrono::duration_cast<std::chrono::nanoseconds>(end - begin).count() / 1e6; // milliseconds
		outputFile << net_cost(MPA_solution, MPA_included_vertices) << "," << MPA_time / 1e3 << "s,";

		if (solution_contain_all_groups(num_vertices(random_graph), MPA_included_vertices, group_graph) == false) {
			cout << "Groups missing in MPA_solution!" << endl;
		}
		if (i > 20 && LV_condition_met(MPA_solution, LV) == false) {
			cout << "LV condition not met in MPA_solution!" << endl;
		}
		connectivity_check_ignore_isolated_vertices(num_vertices(random_graph), MPA_solution);

		begin = std::chrono::high_resolution_clock::now();
		graph PostP_GMLB_solu;
		if (i <= 10) {
			PostP_GMLB_solu = PostP_GMLB(random_graph, group_graph, MPA_solution, MPA_included_vertices, alpha);
		}
		else if (i <= 20) {
			PostP_GMLB_solu = PostP_GMG(random_graph, group_graph, MPA_solution, MPA_included_vertices);
		}
		else if (i <= 30) {
			PostP_GMLB_solu = PostP_GMLB_NWFGSTP(random_graph, group_graph, MPA_solution, MPA_included_vertices, alpha, LV);
		}
		else {
			PostP_GMLB_solu = PostP_GMG_NWFGSTP(random_graph, group_graph, MPA_solution, MPA_included_vertices, LV);
		}
		end = std::chrono::high_resolution_clock::now();
		double PostP_time = std::chrono::duration_cast<std::chrono::nanoseconds>(end - begin).count() / 1e6; // milliseconds
		outputFile << net_cost(PostP_GMLB_solu, MPA_included_vertices) << "," << PostP_time / 1e3 << "s" << endl;
		cout << endl;


		if (solution_contain_all_groups(num_vertices(random_graph), MPA_included_vertices, group_graph) == false ) {
			cout << "Groups missing in PostP_GMLB_solu!" << endl;
		}
		if (i > 20 && LV_condition_met(PostP_GMLB_solu, LV) == false) {
			cout << "LV condition not met in PostP_GMLB_solu!" << endl;
		}
		connectivity_check_ignore_isolated_vertices(num_vertices(random_graph), PostP_GMLB_solu);

	}




}
#pragma endregion MPA_solve_S_T


#pragma region
void create_NWGSTP_WSNs_for_visualization_011paper() {

	// 2D Euclidean_location
	std::vector<std::vector<double>> Euclidean_location_basestation = { { 43,75 }, {10, 70} }; // [x,y]
	std::vector<std::vector<double>> Euclidean_location_sensor = { { 9,4 },{ 49,15 },{ 43,28 },{ 81,35 },{ 18,38 },{ 16,47 }
	,{ 30,63 },{ 10,52 },{ 48,79 },{ 20,88 },{ 47,89 },{ 32,109 },{ 48,119 },{ 41,120 },{ 3,120 },{ 41,156 },{ 23,158 },{ 9,176 } };
	std::vector<std::vector<double>> Euclidean_location_relay = { {25, 40}, { 63,38 },{ 31,16 },{ 35,95 },{ 50,50 }
	,{ 22,65 },{ 20,119 },{ 35,138 },{ 17,138 },{ 0,160 } };
	std::vector<std::vector<double>> Euclidean_location_target = { {10, 28}, {60, 30}, {40, 70}, {50, 130}, {5, 148} }; // , {30,60} 

	// WSN graph
	int R_num = 1; // TR_num types of relays
	std::vector<double> z_coordinate_R = { 0 }; // relays' z coordinates; sensors and base stations' z coordinates are 0
	std::vector<double> r_R = { 40 };
	double r_s = 30;
	double r_b = 40;
	std::vector<double> w_R = { -1e3 };
	double w_R_error_min = -1e2;
	double w_R_error_max = 1e2;
	double w_b = -1e3;
	double w_b_error_min = -1e2;
	double w_b_error_max = 1e2;
	double w_s = -1e3;
	double w_s_error_min = -1e2;
	double w_s_error_max = 1e2;
	double edge_cost_ratio = 1e-2;

	int N = Euclidean_location_basestation.size() + Euclidean_location_sensor.size() + Euclidean_location_relay.size() * R_num;


	std::vector<int> LV(N);
	std::vector<std::vector<double>> visualization_coordinate;
	std::vector<int> node_type(N); // 0:sensor, 100:basestation, 1:relay type 1
	std::vector<double> node_range(N);
	int node_index = 0;


	// two WSN graph; input coordibates, node weights, node_type, node_range
	graph WSN_two_tiered(N);
	for (int i = 0; i < Euclidean_location_basestation.size(); i++) {  // basestation
		std::vector<double> coordinate;
		coordinate.insert(coordinate.end(), Euclidean_location_basestation[i][0]);
		coordinate.insert(coordinate.end(), Euclidean_location_basestation[i][1]);
		coordinate.insert(coordinate.end(), 0);
		visualization_coordinate.insert(visualization_coordinate.end(), coordinate);
		node_type[node_index] = 100;
		node_range[node_index] = r_b;
		int error = w_b_error_min + (rand() % (int)(w_b_error_max - w_b_error_min + 1)); // generate int random number 
		boost::put(boost::vertex_name_t(), WSN_two_tiered, node_index, (w_b + (double)error)); // node weight of base stations
		node_index++;
	}
	for (int i = 0; i < Euclidean_location_sensor.size(); i++) {  // sensor
		std::vector<double> coordinate;
		coordinate.insert(coordinate.end(), Euclidean_location_sensor[i][0]);
		coordinate.insert(coordinate.end(), Euclidean_location_sensor[i][1]);
		coordinate.insert(coordinate.end(), 0);
		visualization_coordinate.insert(visualization_coordinate.end(), coordinate);
		int error = w_s_error_min + (rand() % (int)(w_s_error_max - w_s_error_min + 1)); // generate int random number 
		boost::put(boost::vertex_name_t(), WSN_two_tiered, node_index, (w_s + (double)error)); // node weight of sensor nodes
		LV[node_index] = 1;
		node_type[node_index] = 0;
		node_range[node_index] = r_s;
		node_index++;
	}
	for (int i = 0; i < Euclidean_location_relay.size(); i++) {
		for (int j = 0; j < z_coordinate_R.size(); j++) {
			std::vector<double> coordinate;
			coordinate.insert(coordinate.end(), Euclidean_location_relay[i][0]);
			coordinate.insert(coordinate.end(), Euclidean_location_relay[i][1]);
			coordinate.insert(coordinate.end(), z_coordinate_R[j]);
			visualization_coordinate.insert(visualization_coordinate.end(), coordinate);
			int error = w_R_error_min + (rand() % (int)(w_R_error_max - w_R_error_min + 1)); // generate int random number 
			boost::put(boost::vertex_name_t(), WSN_two_tiered, node_index, (w_R[j] + (double)error));
			node_type[node_index] = j + 1;
			node_range[node_index] = r_R[j];
			node_index++;
		}
	}


	// single WSN graph with node weights
	graph WSN_single_tiered = copy_graph(WSN_two_tiered);


	// add edge to WSN_two_tiered: relay/base to relay/base
	for (int i = 0; i < N; i++) {
		if (node_type[i] > 0) { // i is base station or relay 
			for (int j = 0; j < N; j++) {
				if (node_type[j] > 0) { // base station or relay connects its nearby base station or relay 
					double distance = sqrt(pow(visualization_coordinate[i][0] - visualization_coordinate[j][0], 2) +
						pow(visualization_coordinate[i][1] - visualization_coordinate[j][1], 2));
					if (distance >= 1e-3 && distance <= node_range[i] && distance <= node_range[j]) { // sensor i connects its nearby relay
						double edge_cost = pow(distance, 4)*edge_cost_ratio; // edge cost equation
						boost::add_edge(i, j, edge_cost, WSN_two_tiered);
					}
				}
			}
		}
	}
	std::vector<int> component(N); // vertex i is in component[i]; No.component from 0
	int cpn_num = connected_components(WSN_two_tiered, &component[0]); // the number of component; decrease component
	if (cpn_num == Euclidean_location_sensor.size() + 1) { // WSN_two_tiered is solvable, so, go on!

		// add edge to WSN_two_tiered: sensor to relay
		for (int i = 0; i < N; i++) {
			if (node_type[i] > 0) { // i is base station or relay 
			}
			else { // i is sensor
				for (int j = 0; j < N; j++) {
					if (node_type[j] > 0 && node_type[j] < 100) { // j is relay
						double distance = sqrt(pow(visualization_coordinate[i][0] - visualization_coordinate[j][0], 2) +
							pow(visualization_coordinate[i][1] - visualization_coordinate[j][1], 2));
						if (distance >= 1e-3 && distance <= node_range[i] && distance <= node_range[j]) { // sensor i connects its nearby relay
							double edge_cost = pow(distance, 4)*edge_cost_ratio; // edge cost equation
							boost::add_edge(i, j, edge_cost + 1e8, WSN_two_tiered);
						}
					}
				}
			}
		}

		// connectivity check
		component.clear();
		cpn_num = connected_components(WSN_two_tiered, &component[0]); // the number of component; decrease component
		if (cpn_num == 1) { // TCCG is connected, go on! SCCG must also be connected

			// add edge to WSN_single_tiered
			for (int i = 0; i < N; i++) {
				for (int j = i + 1; j < N; j++) {
					double distance = sqrt(pow(visualization_coordinate[i][0] - visualization_coordinate[j][0], 2) +
						pow(visualization_coordinate[i][1] - visualization_coordinate[j][1], 2));
					if (distance >= 1e-3 && distance <= node_range[i] && distance <= node_range[j]) { // they are at different locations; distance is within two ranges
						double edge_cost = pow(distance, 4)*edge_cost_ratio; // edge cost equation
						boost::add_edge(i, j, edge_cost, WSN_single_tiered);
					}
				}
			}
		}
		else {
			cout << "WSN_two_tiered is Disconnected! Section number: " << cpn_num << endl;
		}
	}
	else {
		cout << "WSN_two_tiered is not solvable! Section number: " << cpn_num - (Euclidean_location_sensor.size()) << endl;
	}



	cout << "V=" << num_vertices(WSN_single_tiered) << " E=" << num_edges(WSN_single_tiered) << endl;
	cout << "V=" << num_vertices(WSN_two_tiered) << " E=" << num_edges(WSN_two_tiered) << endl;


	// save csv
	ofstream outputFile;
	outputFile.setf(ios::fixed);
	outputFile.setf(ios::showpoint);
	outputFile.open("WSN_single_tiered_edge.csv"); // csv file
	outputFile << "Edge,V1,V2" << endl;
	typedef graph::edge_descriptor Edge;
	for (int i = 0; i < N; i++) {
		for (int j = 0; j < i; j++) {
			pair<Edge, bool> ed = boost::edge(i, j, WSN_single_tiered);
			if (ed.second) { // This edge exists!
				outputFile << "E," << i + 1 << "," << j + 1 << endl;
			}
		}
	}
	outputFile.close();
	outputFile.open("WSN_two_tiered_edge.csv"); // csv file
	outputFile << "Edge,V1,V2" << endl;
	typedef graph::edge_descriptor Edge;
	for (int i = 0; i < N; i++) {
		for (int j = 0; j < i; j++) {
			pair<Edge, bool> ed = boost::edge(i, j, WSN_two_tiered);
			if (ed.second) { // This edge exists!
				outputFile << "E," << i + 1 << "," << j + 1 << endl;
			}
		}
	}
	outputFile.close();


	// input groups
	graph group_graph(N + Euclidean_location_target.size() + 1); // each target has a group; all the base station has a group
	for (int i = 0; i < N; i++) {
		if (node_type[i] == 100) {
			boost::add_edge(i, N + 0, 1, group_graph); // group 0 is base station
		}
		else if (node_type[i] == 0) { // i is sensor
			for (int j = 0; j < Euclidean_location_target.size(); j++) {
				double distance = sqrt(pow(visualization_coordinate[i][0] - Euclidean_location_target[j][0], 2) +
					pow(visualization_coordinate[i][1] - Euclidean_location_target[j][1], 2));
				if (distance < r_s) { // target j is in the range
					boost::add_edge(i, N + j + 1, 1, group_graph); // target j is in group j+1; j from 0
				}
			}
		}
	}



	// used to add targets
	int x = 0;
	for (int i = 0; i < N; i++) {
		if (node_type[i] == 0 && in_degree(i, group_graph) == 0) {
			cout << "a useless sensor " << visualization_coordinate[i][0] << "," << visualization_coordinate[i][1] << endl;
			x++;
		}
		else if (node_type[i] == 0 && in_degree(i, group_graph) == 1) {

		}
		else if (node_type[i] == 0 && in_degree(i, group_graph) > 1) {
			cout << "this sensor covers multiple targets" << endl;
		}
	}
	cout << "Non group sensors: " << x << endl;






	// MPA
	std::vector<int> MPA_included_vertices;
	graph MPA_WSN_single_tiered = MPA(WSN_single_tiered, group_graph, MPA_included_vertices);
	graph PostP_WSN_single_tiered = PostP_GMLB(WSN_single_tiered, group_graph, MPA_WSN_single_tiered, MPA_included_vertices, 0);
	graph MPA_WSN_two_tiered = MPA_NWFGSTP(WSN_two_tiered, group_graph, MPA_included_vertices, LV);
	graph PostP_WSN_two_tiered = PostP_GMLB_NWFGSTP(WSN_two_tiered, group_graph, MPA_WSN_two_tiered, MPA_included_vertices, 0, LV);


	// exact
	


	outputFile.open("WSN_single_tiered_edge_after_PostP.csv"); // csv file
	outputFile << "Edge,V1,V2" << endl;
	typedef graph::edge_descriptor Edge;
	for (int i = 0; i < N; i++) {
		for (int j = 0; j < i; j++) {
			pair<Edge, bool> ed = boost::edge(i, j, PostP_WSN_single_tiered);
			if (ed.second) { // This edge exists!
				outputFile << "E," << i + 1 << "," << j + 1 << endl;
			}
		}
	}
	outputFile.close();
	outputFile.open("WSN_two_tiered_edge_after_PostP.csv"); // csv file
	outputFile << "Edge,V1,V2" << endl;
	typedef graph::edge_descriptor Edge;
	for (int i = 0; i < N; i++) {
		for (int j = 0; j < i; j++) {
			pair<Edge, bool> ed = boost::edge(i, j, PostP_WSN_two_tiered);
			if (ed.second) { // This edge exists!
				outputFile << "E," << i + 1 << "," << j + 1 << endl;
			}
		}
	}
	outputFile.close();
	outputFile.open("WSN_vertex.csv"); // csv file
	outputFile << "V,Type,X,Y,Z" << endl;
	for (int i = 0; i < N; i++) {
		outputFile << i + 1 << "," << node_type[i] << "," << visualization_coordinate[i][0] << "," << visualization_coordinate[i][1] << "," << visualization_coordinate[i][2] << endl;
	}
	outputFile.close();
	outputFile.open("WSN_sensor_groups.csv"); // csv file
	typedef boost::graph_traits<graph>::adjacency_iterator AdjacencyIterator;
	AdjacencyIterator ai, a_end;
	for (int i = N + 1; i < num_vertices(group_graph); i++) { // check sensor groups
		boost::tie(ai, a_end) = boost::adjacent_vertices(i, group_graph); // vertices in group i
		for (; ai != a_end; ai++) {
			outputFile << *ai + 1 << ",";
		}
		outputFile << endl;
	}
	outputFile.close();
	outputFile.open("WSN_targets.csv"); // csv file
	for (int i = 0; i < Euclidean_location_target.size(); i++) {
		outputFile << Euclidean_location_target[i][0] << "," << Euclidean_location_target[i][1] << endl;
	}
	outputFile.close();

}
#pragma endregion create_NWGSTP_WSNs_for_visualization_011paper


#pragma region
void MPA_with_G1_is_better() {

	int iteration_times = 100;
	int V = 100, E = 1000, G = 20;
	string save_name = "MPA_approximation_ratio_V_" + to_string(V) + "_E_" + to_string(E) + "_G_" + to_string(G) + ".csv";
	int g_size_min = 1;
	int g_size_max = 3;
	double alpha = 1;

	ofstream outputFile;
	outputFile.precision(4);
	outputFile.setf(ios::fixed);
	outputFile.setf(ios::showpoint);
	outputFile.open(save_name);
	outputFile << "practice_approximation_ratio" << endl;

	int times = 0;
	int MPA_with_G1_is_better_time = 0;
	while (times < iteration_times) {
		times++;

		graph random_graph, group_graph, initial_tree;
		generate_random_NWGSTP_graphs(V, E, G, g_size_min, g_size_max, random_graph, group_graph);

		std::vector<int> MPA_included_vertices;
		graph MPA_solution = MPA(random_graph, group_graph, MPA_included_vertices);
		//cout << "MPA_solution cost: " << net_cost(MPA_solution, MPA_included_vertices) << endl;

		std::vector<int> MPA_wihtout_G1_included_vertices;
		graph MPA_wihtout_G1_solution = MPA_wihtout_G1(random_graph, group_graph, MPA_wihtout_G1_included_vertices);
		//cout << "MPA_wihtout_G1_solution cost: " << net_cost(MPA_wihtout_G1_solution, MPA_wihtout_G1_included_vertices) << endl;

		if (net_cost(MPA_solution, MPA_included_vertices) < net_cost(MPA_wihtout_G1_solution, MPA_wihtout_G1_included_vertices)) {
			MPA_with_G1_is_better_time++;
		}

	}

	cout << "MPA_with_G1_is_better_ratio: " << (double) MPA_with_G1_is_better_time / iteration_times * 100 << "%" << endl;


}
#pragma endregion MPA_with_G1_is_better


int main()
{
	srand(time(NULL));

	MPA_approximation_ratio_Exact_CountCompulsory();

	std::cout << "END" << endl;
	getchar();
}


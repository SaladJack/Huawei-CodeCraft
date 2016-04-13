#include "route.h"
#include "lib_record.h"
#include <assert.h>
#include <time.h>
#include <sys/timeb.h>
#include <errno.h>
#include <unistd.h>
#include <signal.h>
#include<cstdio>
#include <functional>
#include<cstring>
#include<algorithm>
#include<iomanip>
#include<sstream>
#include<iostream>
#include<string>
#include<vector>
#include<queue>
#include<cmath>
#include<set>
#include<map>
#include<bitset>
#include<stack>
#include<list>
#include<cstdlib>
#include<limits>

const int infinity = 1061109566;
const double limit = 9.0;
const int max_vertex = 610;
const int max_edge = 372100;
using namespace::std;
time_t start_time = time(NULL);
/*
vector<int> optimal_path[max_vertex][max_vertex];
vector<int> suboptimal_path[max_vertex][max_vertex];
int optimal_path_dist[max_vertex][max_vertex];
int suboptimal_path_dist[max_vertex][max_vertex];
*/
int dist_to_dest[max_vertex];
int N = 0;
int tmpEdges[max_vertex][max_vertex];
int shortestPath[max_vertex];
bool marked[max_vertex];
bool pai_chu[max_vertex]; 
bool visitedB[max_vertex]; 
int jing_bi_xu; 
vector<int> information;
int pathLen = 0;
queue<int> que; 
vector<int> path[max_vertex][max_vertex][2];
int dist[max_vertex][max_vertex][2];
vector<int> my_answer;
int try_path[max_vertex];
bool is_edge_removed[max_edge], is_node_removed[max_vertex];
int bound = infinity;
bool is_visited[max_vertex];

class Graph
{
private:	
	void add(int a,int _index,int _head,int _cost)
	{
		Edge e;
		e.index=_index;e.head=_head;e.cost=_cost;
		tu[a].push_back(e);
	}
public:
	bool *mark;
	int numVertex, numEdge;
	struct Edge
	{
	int index, head, cost;
	};
	void Init(int n) {
		int i;
		numVertex = n;
		numEdge = 0;
		mark = new bool[n];
		for (i = 0; i<numVertex; i++)
			mark[i] = false;
	}
	map<pair<int,int>,int> vertex_pair_to_edge;
	vector<Edge> tu[max_vertex];
	map<pair<int,int>,int>::iterator it;
	int edge_cost[max_edge];
    int necessary_vertex[max_vertex], NN;
    bool must_or_not[max_vertex];
    int  S, E;
    Graph()
    {
    	memset(must_or_not, false, sizeof(must_or_not));
    	NN=0;
	}
	void tryAdd(int _suoyin,int _qidian,int _zhongdian,int _haofei)
	{
		it = vertex_pair_to_edge.find(pair<int,int>(_qidian, _zhongdian));
		if (it == vertex_pair_to_edge.end()) {
            vertex_pair_to_edge[pair<int,int>(_qidian, _zhongdian)] = _suoyin;
		} else if(edge_cost[it->second] > _haofei){
            it->second = _suoyin;
		}
		edge_cost[_suoyin] = _haofei;
	}
	void setNecessary(int vertex)
	{
		must_or_not[vertex] = true;
    	necessary_vertex[NN] = vertex;
    	++NN;
    	if(NN==1)
    		S=vertex;
    	if(NN==2)
    		E=vertex;
	}
	int weight(int i, int j) {
		it=vertex_pair_to_edge.find(pair<int,int>(i,j));
		return edge_cost[it->second];
	}
	void generate()
	{
		for (it = vertex_pair_to_edge.begin(); it != vertex_pair_to_edge.end(); ++ it) {
        int m = it->first.first, n = it->first.second;
        int index = it->second, cost = edge_cost[index];
        add(m,index, n, cost);
    }
	}
	bool getMark(int v) { return mark[v]; }
	void setMark(int v, bool val) { mark[v] = val; }
	friend int find(int, int, vector<int> &);
	friend bool isOK(int, int);
};

Graph gra;
Graph re_gra;
class DijkElem
{
public:
	int vertex, distance;
	DijkElem()
	{
		vertex = -1;
		distance = -1;
	}
	DijkElem(int v, int d)
	{
		vertex = v;
		distance = d;
	}
	bool operator<(DijkElem kk)
	{
		return distance < kk.distance;
	}
	bool operator>(DijkElem kk)
	{
		return distance > kk.distance;
	}
};
bool operator>(const DijkElem jj, const DijkElem kk)
{
	return jj.distance > kk.distance;
}
void Dijkstra(Graph& G, int s, int* d, int* p)
{
	int i, v, w;
	DijkElem temp;
	temp.distance = 0;
	temp.vertex = s;
	priority_queue<DijkElem, vector<DijkElem>, greater<DijkElem> >H;
	H.push(temp);
	for (i = 0;i < max_vertex;i++)
	{
		G.setMark(i, false);
		p[i] = -1;
		d[i] = (infinity);
	}
	d[s] = 0;
	for (i = 0;i < max_vertex;i++)
	{
		do {
			if (H.size() == 0)
				return;
			temp = H.top();
			H.pop();
			v = temp.vertex;
		} while (G.getMark(v) == true);
		G.setMark(v, true);
		if (d[v] ==infinity)
			return;
		for (int mm=0;mm<G.tu[v].size();++mm)
		{
			w=G.tu[v][mm].head;
			if (d[w]>(d[v] + G.weight(v, w)))
			{
				d[w] = d[v] + G.weight(v, w);
				p[w] = v;
				temp.distance = d[w];
				temp.vertex = w;
				H.push(temp);
			}
	}
	}
}
string tostr(int x)
{
	string s;
	stringstream ss;
	ss << x;
	ss >> s;
	return s;
}
class Compass
{
private:
	struct TE
	{
    int total, bri, state;
    vector<int> detail;
    TE(int _tot, int _index, int _used):
    total(_tot), bri(_index), state(_used){detail.clear();}
	};
	struct Alternative
	{
    int how_long, end, number;
    Alternative(int _length, int _end, int _number):how_long(_length), end(_end), number(_number){}
    bool operator < (const Alternative & road) const {
        if (road.how_long == how_long) 
        	return number < road.number;
        return how_long < road.how_long;
    }
	};	
		void deleteFront(vector<int> *_path, int i, int k){
    for (int a = 0; a < k; a++) 
	{
    	bool mark=true;
    	for(unsigned int j = 0; j + 1 < _path[a].size() && j + 1 < _path[k-1].size() && j <= i; ++j)
    		if(_path[a][i] != _path[k-1][i]) mark=false;
        if(mark) {
            int idx = gra.vertex_pair_to_edge[pair<int,int>(_path[a][i], _path[a][i+1])];
            is_edge_removed[idx] = true;
        }
    }
    for (int a = 0; a < i; a++) {
        is_node_removed[_path[k-1][a]] = true;
    }
}
void recoverFront(vector<int> *_path, int i, int k){
    for (int a = 0; a < k; a++) 
	{
    	bool mark=true;
    	for(unsigned int j = 0; j + 1 < _path[a].size() && j + 1 < _path[k-1].size() && j <= i; ++j)
    		if(_path[a][i] != _path[k-1][i]) mark=false;
        if(mark) {
            int idx = gra.vertex_pair_to_edge[pair<int,int>(_path[a][i], _path[a][i+1])];
            is_edge_removed[idx] = false;
        }
    }
    for (int a = 0; a < i; a++) {
        is_node_removed[_path[k-1][a]] = false;
    }
}
bool sToV(char *src,int *output)
{
	int ten[]={1,10,100,1000,10000,100000,1000000};
	int index=0;
	int begin=0;
	int end;
	int bit=0;

	while(bit<4)
	{
		if(src[index]==','||src[index]=='\n'||src[index]==(char)(NULL))
		{
			end=index-1;
			int sum=0;
			for(int i=end;i>=begin;i--)
			{
				sum+=(src[i]-'0')*ten[end-i];
			}
			output[bit]=sum;
			bit++;
			begin=index+1;
		}
		index++;

	}
	if(src[index-1]==(char)(NULL))
	{
		return true;
		
	}
	else
	{
		return false;
		

	}
}
int find(int start, int end, vector<int> &_road) 
	{
	int how_long[max_vertex], prev[max_vertex];
	bool is_node_in_queue[max_vertex];
	queue<int> queue;
    memset(how_long, 0x3f, sizeof(how_long));
    memset(prev, -1, sizeof(prev));
    memset(is_node_in_queue, false, sizeof(is_node_in_queue));
    how_long[start] = 0; prev[start] = -1;
    is_node_in_queue[start] = true;
    queue.push(start);

    while(!queue.empty()) {
        int u = queue.front();
        queue.pop();
        is_node_in_queue[u] = false;
        for (int i = 0; i < (int)gra.tu[u].size(); ++i) {
            Graph::Edge &e = gra.tu[u][i];
            if (is_edge_removed[e.index] || is_node_removed[e.head]) continue;
            if (how_long[e.head] > how_long[u] + e.cost) {
                how_long[e.head] = how_long[u] + e.cost;
                prev[e.head] = u;
                if (!is_node_in_queue[e.head] && !gra.must_or_not[e.head]) {
                    is_node_in_queue[e.head] = true;
                    queue.push(e.head);
                }
            }
        }
    }
    _road.clear();
    if(how_long[end] >= infinity) return how_long[end];
    for(int u = end; ~u; u = prev[u]) {
        _road.push_back(u);
    }
    return how_long[end];
	}
	int kym;
public:
	vector<Alternative> lists[max_vertex];
	vector<TE> TE_list;
	void set(int a)
	{
		kym=a;
	}
	void addAlternative(int _which,int _dist,int _end,int _number)
	{
		lists[_which].push_back(Alternative(_dist, _end, _number));
	}
	Compass()
	{
		kym=0;
	} 
	void adjust(int _start)
	{
		sort(lists[_start].begin(), lists[_start].end());
		if(getSize(_start)>1&&kym<16)
		{
		Alternative temp = lists[_start][0];
        lists[_start][0] = lists[_start][1];
        lists[_start][1] = temp;  
		++kym;    
    	}
	}
	void getCompass(int start, int end){
    int branch[4];
    memset(branch, 0, sizeof(branch));
    vector<int> *_road = path[start][end];
    int *_dist = dist[start][end];

    int distance = find(start, end, _road[0]);
    if (distance >= infinity) return ;
    reverse(_road[0].begin(), _road[0].end());
    _dist[0] = distance;
    TE_list.clear();

    for (int number = 1; number < 2; ++ number) {
        for (int i = branch[number-1]; i + 1 < (int)_road[number-1].size(); i++) {
            int spurNode = _road[number-1][i];
            deleteFront(_road, i, number);

            TE_list.push_back(TE(0, i, 0));
            TE &tet = TE_list.back();
            vector<int> &current_path_detail = tet.detail;
            distance = find(spurNode, end, current_path_detail);
            recoverFront(_road, i, number);

            if(distance >= infinity) {
                TE_list.pop_back(); continue;
            }
            for(int road = i-1; road >= 0; -- road) current_path_detail.push_back(_road[number-1][road]);
            reverse(current_path_detail.begin(), current_path_detail.end());
            for (int a = 1; a < (int)current_path_detail.size(); ++a) {
                tet.total += gra.edge_cost[gra.vertex_pair_to_edge[pair<int,int>(current_path_detail[a-1], current_path_detail[a])]];
            }
        }
        int index = -1;
    for (int i = 0; i < (int)TE_list.size(); ++i)
    if(TE_list[i].state == 0){
        if(index == -1 || TE_list[index].total > TE_list[i].total)
        index = i;
    }
    if(index >= 0) TE_list[index].state = 1;
    	for (int i = 0; i < (int)TE_list.size(); ++i)
    		if(TE_list[i].state == 0)
			{
        		if(index == -1 || TE_list[index].total > TE_list[i].total)
        		index = i;
   			}
    	if(index >= 0) TE_list[index].state = 1;
        if(index == -1) return ;
        _road[number].resize(TE_list[index].detail.size());
        copy(TE_list[index].detail.begin(), TE_list[index].detail.end(), _road[number].begin());
        dist[start][end][number] = TE_list[index].total;
        branch[number] = TE_list[index].bri;
    	}
	}
	int getSize(int what)
	{
		return lists[what].size();
	}
};
Compass compass;

bool isOK(int already, int left){
    if (left < 0) return false;
    if (left == 0) return true;

    bool _vis[max_vertex] = {0};
    queue<int> q;
    while(!q.empty()) q.pop();
    q.push(already); _vis[already] = 1;
    while(!q.empty()){
        int u = q.front();
        q.pop();
        for(int i = 0; i < (int)gra.tu[u].size(); ++i){
            Graph::Edge &e = gra.tu[u][i];
            if(is_visited[e.head] || _vis[e.head]) continue;
            if (gra.must_or_not[e.head]) --left;
            if (left == 0) return true;
            _vis[e.head] = 1;
            q.push(e.head);
        }
    }
    return left == 0;
}
bool tryGo(int already, int source, int cost, int left) {
    if (difftime(time(NULL), start_time) > limit) {
        return true;
    }
    if (cost >= bound) return false;
    if (source == gra.E) {
        if (left==0)
        {
        bound = cost;
        my_answer.resize(already);
        copy(try_path, try_path + already, my_answer.begin());
    	}
        return false;
    }
	int tem=compass.getSize(source);
    for(int i = 0; i < tem; ++i) {
        int distance = compass.lists[source][i].how_long;
        int u = compass.lists[source][i].end;
        int _number = compass.lists[source][i].number;
        vector<int>&road = path[source][u][_number];
        if(road.size() == 0) continue;
        bool mark = false;
        for (int j = 1; j < (int)road.size(); ++j)
        if (is_visited[road[j]]) {
            mark = true; 
			break;
        }
        if (mark) continue;
        int must_num = 0;
        for (int j = 1; j < (int)road.size(); ++j) {
            is_visited[road[j]] = true;
            try_path[already+j-1] = road[j];
            if(gra.must_or_not[road[j]]) must_num++;
        }
        if (isOK(u, left - 1)) {
            if(tryGo(already + road.size() - 1, u, cost + distance, left - 1))
            return true;
        }
        for (int j = 1; j < (int)road.size(); ++j) is_visited[road[j]] = 0;
    }
    return false;
}
void reSPFA() {
    memset(marked, 0, sizeof(marked));
	que.push(re_gra.S);
	marked[re_gra.S] = true;
	while (!que.empty()) {
		int u = que.front();
		que.pop();
		marked[u] = false;
		for (int c = 0; c < re_gra.tu[u].size(); ++c) {
			int w = re_gra.tu[u][c].cost;
			int v = re_gra.tu[u][c].head;
			if (dist_to_dest[v] == 0 || dist_to_dest[v] > dist_to_dest[u] + w) {
				dist_to_dest[v] = dist_to_dest[u] + w;
				if (marked[v] == false) {
					que.push(v);
					marked[v] = true;
				}
			}
		}
	}
}
struct Node2 {
    int b, dis;
};
bool comp(const Node2 &u, const Node2 &v) {
    return u.dis < v.dis;
}
bool check(int start) {
	memset(marked, 0, sizeof(marked));

	que.push(start);
	marked[start] = true;

	while (!que.empty()) {
		int u = que.front();
		que.pop();
		for (int c = 0; c < gra.tu[u].size(); ++c) {
			int v = gra.tu[u][c].head;
			if (pai_chu[v]) continue;
			if (marked[v] == false) {
				que.push(v);
				marked[v] = true;
			}
		}
	}
	for (int i = 2; i < gra.NN; i++) {
	    int b = gra.necessary_vertex[i];
		if (!visitedB[b] && marked[b] == false)
			return false;
	}
	if (marked[gra.E] == false) return false;
	return true;
}
class minheap {
private:
	int* Heap;
	int maxsize;
	int n;
	int* distances;
	bool* is_in;
	void siftdown(int pos) {
		while (!isLeaf(pos)) {
			int j = leftchild(pos); int rc = rightchild(pos);
			if ((rc < n) && (distances[Heap[rc]]<distances[Heap[j]]))
				j = rc;
			if (distances[Heap[pos]]<distances[Heap[j]]) return;
			swap(Heap[pos], Heap[j]);
			pos = j;
		}
	}
public:
	minheap(int* h, int num, int max,int* di,bool* wo)
	{
		Heap = h; n = num; maxsize = max;distances=di; is_in=wo;buildHeap();
	}
	int size() const
	{
		return n;
	}
	bool isLeaf(int pos) const
	{
		return (pos >= n / 2) && (pos < n);
	}
	int leftchild(int pos) const
	{
		return 2 * pos + 1;
	}
	int rightchild(int pos) const
	{
		return 2 * pos + 2;
	}
	int parent(int pos) const
	{
		return (pos - 1) / 2;
	}
	void buildHeap()
	{
		for (int i = n / 2 - 1; i >= 0; i--) siftdown(i);
	}
	void insert(const int& it) {
		if (n >= maxsize||is_in[it])
			return;
		int curr = n++;
		is_in[it]=true;
		Heap[curr] = it;
		while ((curr != 0) &&
			(distances[Heap[curr]]<distances[Heap[parent(curr)]])) {
			swap(Heap[curr], Heap[parent(curr)]);
			curr = parent(curr);
		}
	}
	int removefirst() {
		if (n > 0)
		{
			swap(Heap[0], Heap[--n]);
			if (n != 0) siftdown(0);
			return Heap[n];
		}
	}
};
void runAndCompute(int start) {
    if (difftime(time(NULL), start_time) > limit) {
        return;
    }
    if (!check(start)) return;
    int *distances = new int[N];
    int *parents = new int[N];
    /*
    int *temp = new int[N];
    bool *wo = new bool[N];
    memset(wo,0,sizeof(wo));
    */
    memset(distances,0,sizeof(int)*N);
    memset(parents,-1,sizeof(int)*N);
    /*
    minheap mh(temp,0,N,distances,wo);
    mh.insert(start);
    int jing_guo = jing_bi_xu;
    while(mh.size())
    {
    	int u=mh.removefirst();
    	cout<<u<<endl;
        if (u == gra.E) {
            if (jing_guo == gra.NN-2) break;
            continue;
        }
        if (u != start && gra.must_or_not[u]) {
            if (++jing_guo == gra.NN-2) break;
            continue;
        }
        for (int c = 0; c < gra.tu[u].size(); ++c) {
            int w = gra.tu[u][c].cost;
            int v = gra.tu[u][c].head;
            if (pai_chu[v]) continue;
            if (distances[v] == 0) {
                distances[v] = distances[u] + w;
                parents[v] = u;
                mh.insert(v);
            } else if (distances[v] > distances[u] + w){
                distances[v] = distances[u] + w;
                parents[v] = u;
            }
        }
	}
	*/
    set<int> se;
    se.insert(start);
    parents[start] = start;
    int jing_guo = jing_bi_xu;
    while (!se.empty()) {
        int mindis = infinity, u;
        for (set<int>::iterator it = se.begin(); it != se.end(); ++it) {
            if (mindis > distances[*it]) {
                mindis = distances[*it];
                u = *it;
            }
        }
        se.erase(u);
        if (u == gra.E) {
            if (jing_guo == gra.NN-2) break;
            continue;
        }
        if (u != start && gra.must_or_not[u]) {
            if (++jing_guo == gra.NN-2) break;
            continue;
        }
        for (int c = 0; c < gra.tu[u].size(); ++c) {
            int w = gra.tu[u][c].cost;
            int v = gra.tu[u][c].head;
            if (pai_chu[v]) continue;
            if (distances[v] == 0) {
                distances[v] = distances[u] + w;
                parents[v] = u;
                se.insert(v);
            } else if (distances[v] > distances[u] + w){
                distances[v] = distances[u] + w;
                parents[v] = u;
            }
        }
    }
    if (gra.NN-2 == jing_bi_xu) {
        vector<int> the_left;
        int p = gra.E;
        while (parents[p] != p) {
            the_left.push_back(p);
            p = parents[p];
        }
        bound = information[0] + distances[gra.E];
        pathLen = information.size() + the_left.size() - 1;
        for (vector<int>::size_type i = 1; i < information.size(); ++i)
            shortestPath[i - 1] = information[i];
        for (vector<int>::size_type i = 0; i < the_left.size(); ++i)
            shortestPath[i + information.size() - 1] = the_left[the_left.size() - i - 1];
        return;
    }
    Node2 *temp_must = new Node2[gra.NN-2 - jing_bi_xu];
    int how_many_must = 0;
    for (int i = 2; i < gra.NN; i++) {
        int b = gra.necessary_vertex[i];
        if (visitedB[b] || dist_to_dest[b] == 0 || distances[b] == 0
            || (information[0] + distances[b] + dist_to_dest[b] >= bound)
            )
            continue;
        temp_must[how_many_must].b = b;
        temp_must[how_many_must].dis = information[0] + distances[b];
        how_many_must++;
    }
    sort(temp_must, temp_must + how_many_must, comp);
    vector<int> the_left;
    for (int bi = 0; bi < how_many_must; ++bi) {
        int b = temp_must[bi].b;
        the_left.clear();
        int p = b;
        while (parents[p] != p) {
            the_left.push_back(p);
            p = parents[p];
        }
        information[0] += distances[b];
        for (int i = the_left.size() - 1; i >= 0; --i) {
            information.push_back(the_left[i]);
            pai_chu[the_left[i]] = true;
        }
        visitedB[b] = true;
        jing_bi_xu++;
        runAndCompute(b);
        visitedB[b] = false;
        jing_bi_xu--;
        for (int i = the_left.size() - 1; i >= 0; --i) {
            information.pop_back();
            pai_chu[the_left[i]] = false;
        }
        information[0] -= distances[b];
    }
    delete[] temp_must;
    /*
    delete[] temp;
    delete[] wo;
    */
    delete[] parents;
    delete[] distances;
}
void search_route(char *topo[5000], int edge_num, char *demand) {
	int _suoyin,_qidian,_zhongdian,_haofei;
	char fenge;
	stringstream stream;
	for(int i=0;i<edge_num;++i)
	{
		sscanf(topo[i], "%d,%d,%d,%d", &_suoyin, &_qidian, &_zhongdian, &_haofei);
		if(_qidian==_zhongdian)
			continue;
		N = max(N, max(_qidian, _zhongdian) + 1);
		gra.tryAdd(_suoyin,_qidian,_zhongdian,_haofei);
		re_gra.tryAdd(_suoyin,_zhongdian,_qidian,_haofei);
	}
	stream<<demand;
	stream>>_qidian>>fenge>>_zhongdian;
	gra.setNecessary(_qidian);
	gra.setNecessary(_zhongdian);
	re_gra.setNecessary(_zhongdian);
	re_gra.setNecessary(_qidian);
	while(stream >> fenge >> _zhongdian) {
        gra.setNecessary(_zhongdian);
        re_gra.setNecessary(_zhongdian);
	}
	gra.generate();
	re_gra.generate();
	cout<<gra.NN<<endl;
	if((edge_num>=500&&edge_num<=1200)||(edge_num==2000&&gra.NN>=25))
	{
    	memset(visitedB, 0, sizeof(visitedB));
    	jing_bi_xu = 0;
    	memset(pai_chu, 0, sizeof(pai_chu));
    	pai_chu[gra.S] = true;
    	information.clear();
    	information.push_back(0);  
    	information.push_back(gra.S);  
    	memset(dist_to_dest, 0, sizeof(dist_to_dest));
    	reSPFA();
    	runAndCompute(gra.S);
    	for (int i = 0; i < pathLen - 1; i++)
    	
	}
	else
	{
		for (int i = 0; i < gra.NN; ++i)
    for (int j = 0; j < gra.NN; ++j)
    if(i != j){
        int start = gra.necessary_vertex[i], end = gra.necessary_vertex[j];
        compass.getCompass(start, end);
        for (int number = 0; number < 2; ++number) {
            vector<int> &road = path[start][end][number];
            if (road.size()) {
                compass.addAlternative(start,dist[start][end][number], end, number);
            }
        }
    }
    compass.set(2);
    for (int i = 0; i < gra.NN; ++i) {
        int start = gra.necessary_vertex[i];
        compass.adjust(start);
    }
    vector<int> temporary;
    is_visited[gra.S] = 1;try_path[0] = gra.S;
    tryGo(1, gra.S, 0, gra.NN-1);
    for (unsigned int i = 1; i < my_answer.size(); ++i)
	{
        int u = my_answer[i-1], v = my_answer[i];
        int index = gra.vertex_pair_to_edge[pair<int,int>(u,v)];
        record_result(index);
    }
	}
}

#include<iostream>
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <time.h>
#include <string>
#include <string.h>
#include <map>
#include <fstream>
#include <vector>
#include <cmath>
#include <random>
#include <algorithm>
#include <chrono>
#include <set>
#include<utility>  
#include<stack>  
#include <list>
#include <unordered_set>  
#include <queue>
#include<unordered_map>  

#include<bitset>  
#define PI acos(-1.0)  
#define INF 0x3f3f3f3f  
#define LL long long  
#define Pair pair<LL,LL> 

LL quickPow(LL a,LL b){ LL res=1; while(b){if(b&1)res*=a; a*=a; b>>=1;} return res; }  
LL quickModPow(LL a,LL b,LL mod){ LL res=1; a=a%mod; while(b){if(b&1)res=(a*res)%mod; a=(a*a)%mod; b>>=1;} return res; }  
LL getInv(LL a,LL mod){ return quickModPow(a,mod-2,mod); }  
LL GCD(LL x,LL y){ return !y?x:GCD(y,x%y); }  
LL LCM(LL x,LL y){ return x/GCD(x,y)*y; }  
const double EPS = 1E-10;  
const int MOD = 998244353;  
const int N = 30000+5;  
const int dx[] = {-1,1,0,0,1,-1,1,1};  
const int dy[] = {0,0,-1,1,-1,1,-1,1};  
using namespace std; 
#define MAXLINE       500   /* max length of input line */
#define K             1000

int n, m; /* number of nodes, arcs */

double epsilon=0.2;
double infharm;
vector<string> username;

map<string, int> user2ID;	// a map from username to userid
map<int ,string> userID_Name;
vector<int> InputEdges;		//
vector<double> EdgeProb;	//propagation probability
map<string, vector<double> > NodeProb;	//persuasion probability
map<string, long double> pa;
map<string, long double> pb;
map<string, int> in_deg;			//in-degree
map<string, double> viewpoint;	//viewpoint of user

//spreaders 
vector<string> Sh;	
vector<string> Sb;
map<int, queue<int> > spreader;


struct MAP {  
    struct Edge {  
        int to, next;  
    } edge[N << 1];  
    int tot, head[N];  
    void addEdge(int x, int y) {  
        edge[++tot].to = y;  
        edge[tot].next = head[x];  
        head[x] = tot;  
    }  
    void clear(){
    	tot=0;
    	memset(head, 0, sizeof(head));  
    	memset(edge, 0, sizeof(edge)); 
	}
};  
 
MAP G, GF;             
MAP dfsTree, dfsTreeF;  
MAP dominate;          //dominator tree
	  
MAP xx;   
 
int father[N];          // father node
int dfn[N], id[N], tim; 
vector<int> subtree[N+1]; // subtree of each node

//results
set<int> B_h;
set<int> B_b;
set<int> B_f;
set<int> B_b_lower;
set<int> B_b_upper;

vector<list<pair<int,double> > > adj_out; 
vector<list<pair<int,double> > > adj_in; 


double a_rand(){
    double random_number = static_cast<double>(rand()) / static_cast<double>(RAND_MAX);
    return random_number;
}


void readGraph(const char* file){
	//readfile, obtain vertexs edges
	int x,y;
	int count_edges=0;
	int count_vertices=0;
	string user_a,user_b;
	long double prob_edge;
	long double prob_a,prob_b;
	
	
	
	map<string, int>::iterator it;
	ifstream infile(file);
	
	while(infile>>user_a>>user_b>>prob_a>>prob_b) {
		//for a
		it=user2ID.find(user_a);
		if(it!=user2ID.end()){
			//username.push_back(it->first);
			x=it->second;
			pa[user_a]+=prob_a;
			pb[user_a]+=prob_b;
		}
		else{
			username.push_back(user_a);
			user2ID[user_a]=count_vertices;
			x=count_vertices++;
			pa[user_a]=prob_a;
			pb[user_a]=prob_b;
		}
		
		//for b
		it=user2ID.find(user_b);
		if(it!=user2ID.end()){
			//username.push_back(it->first);
			y=it->second;
			in_deg[user_b]+=1;

		}
		else{
			username.push_back(user_b);
			user2ID[user_b]=count_vertices;
			y=count_vertices++;
			in_deg[user_b]=1;

		}		
		
		
		
		count_edges++;
		InputEdges.push_back(x);
		InputEdges.push_back(y);	
	}
	
	n=count_vertices;
	m=count_edges;
	
	cout<<"number of users:"<<n<<" number of edges:"<<m<<"\n";
	
	
	//viewpoint
	map<string, long double>::iterator it_for_pa;
	map<string, long double>::iterator it_for_pb;
	vector<string>::iterator it_vector;
	
	unsigned seed = std::chrono::system_clock::now().time_since_epoch().count();  
    std::mt19937 gen(seed);  
  
    // uniform distribution  
    std::uniform_real_distribution<> dis(-1.0, 1.0);  
  
    // random number
    
	double step=0.2;
	for(it_vector=username.begin();it_vector!=username.end();it_vector++)
	{
		double randomNumber = dis(gen);
		double x=round(randomNumber * 10) / 10;
		viewpoint[*it_vector]=round(randomNumber * 10) / 10;
		
	}
		
	for(it_for_pa=pa.begin(),it_for_pb=pb.begin();it_for_pa!=pa.end();it_for_pa++,it_for_pb++){	
		viewpoint[it_for_pa->first]=(it_for_pa->second*2)/(it_for_pa->second+it_for_pb->second)-1;
		viewpoint[it_for_pa->first]=round(viewpoint[it_for_pa->first] * 10) / 10;
	}
	
	//EdgeProb
	ifstream infile2(file);
	while(infile2>>user_a>>user_b>>prob_a>>prob_b){
		EdgeProb.push_back(1.0/in_deg[user_b]);
	}
	
	if(adj_out.size()<n) adj_out.resize(n);
	
	//outdegree adjacency table
	for (int j=0; j<InputEdges.size(); j+=2){
		//edge x -> y
		x = InputEdges.at(j);	 
		y = InputEdges.at(j+1);
		int i=j/2;
		adj_out[x].push_back(pair<int,double>(y,EdgeProb[i]));
	}
	adj_in.resize(n); 
	//indegree adjacency table
	for(int j=0;j<InputEdges.size();j+=2){
		//edge x -> y
		x=InputEdges.at(j);
		y=InputEdges.at(j+1);
		int i=j/2;
		adj_in[y].push_back(pair<int,double>(x,EdgeProb[i])); 
	} 

	
	//userID_Name;
	for(map<string, int>::iterator it_map=user2ID.begin();it_map!=user2ID.end();it_map++){
		userID_Name[it_map->second]=it_map->first;
	}
	
	
	fprintf(stderr, "END reading graph (%s).\n", file); 
	
	

}


void readGraph2(const char* file){
	//readfile, obtain vertexs edges
	int x,y;
	int count_edges=0;
	int count_vertices=0;
	string user_a,user_b;
	long double prob_edge;
	//long double prob_a,prob_b;
	
	
	
	map<string, int>::iterator it;
	ifstream infile(file);
	
	while(infile>>user_a>>user_b) {
		//for a
		it=user2ID.find(user_a);
		if(it!=user2ID.end()){
			//username.push_back(it->first);
			x=it->second;
			
		}
		else{
			username.push_back(user_a);
			user2ID[user_a]=count_vertices;
			x=count_vertices++;
			
		}
		
		//for b
		it=user2ID.find(user_b);
		if(it!=user2ID.end()){
			//username.push_back(it->first);
			y=it->second;
			in_deg[user_b]+=1;

		}
		else{
			username.push_back(user_b);
			user2ID[user_b]=count_vertices;
			y=count_vertices++;
			in_deg[user_b]=1;

		}		
		
		
		
		count_edges++;
		InputEdges.push_back(x);
		InputEdges.push_back(y);	
	}
	
	n=count_vertices;
	m=count_edges;
	
	cout<<"number of users:"<<n<<" number of edges:"<<m<<"\n";
	
	
	//viewpoint
	vector<string>::iterator it_vector;
	
	// uniform distribution 
	unsigned seed = std::chrono::system_clock::now().time_since_epoch().count();  
    std::mt19937 gen(seed);  
  
    std::uniform_real_distribution<> dis(-1.0, 1.0);  
    
	
	for(it_vector=username.begin();it_vector!=username.end();it_vector++)
	{
		double randomNumber = dis(gen);
		viewpoint[*it_vector]=round(randomNumber * 10) / 10;
	}

	//EdgeProb
	ifstream infile2(file);
	while(infile2>>user_a>>user_b){
		EdgeProb.push_back(1.0/in_deg[user_b]);
	}
	
	if(adj_out.size()<n) adj_out.resize(n);
	//outdegree adjacency table	 
	for (int j=0; j<InputEdges.size(); j+=2){
		//edge x -> y
		x = InputEdges.at(j);	 
		y = InputEdges.at(j+1);
		int i=j/2;
		adj_out[x].push_back(pair<int,double>(y,EdgeProb[i]));
	}
	adj_in.resize(n); 
	//indegree adjacency table
	for(int j=0;j<InputEdges.size();j+=2){
		//edge x -> y
		x=InputEdges.at(j);
		y=InputEdges.at(j+1);
		int i=j/2;
 
		adj_in[y].push_back(pair<int,double>(x,EdgeProb[i])); 
	} 

	

	
	//userID_Name;
	for(map<string, int>::iterator it_map=user2ID.begin();it_map!=user2ID.end();it_map++){
		userID_Name[it_map->second]=it_map->first;
	}
	
	
	fprintf(stderr, "END reading graph (%s).\n", file); 
	
	

}

//undirected graph
void readGraph3(const char* file){
	//readfile, obtain vertexs edges
	int x,y;
	int count_edges=0;
	int count_vertices=0;
	string user_a,user_b;
	long double prob_edge;
	long double prob_a,prob_b;
	
	
	
	map<string, int>::iterator it;
	ifstream infile(file);
	
	while(infile>>user_a>>user_b) {
		//for a
		it=user2ID.find(user_a);
		if(it!=user2ID.end()){
			x=it->second;

		}
		else{
			username.push_back(user_a);
			user2ID[user_a]=count_vertices;
			x=count_vertices++;

		}
		
		//for b
		it=user2ID.find(user_b);
		if(it!=user2ID.end()){
			y=it->second;
			in_deg[user_b]+=1;

		}
		else{
			username.push_back(user_b);
			user2ID[user_b]=count_vertices;
			y=count_vertices++;
			in_deg[user_b]=1;

		}		
		
		
		
		count_edges++;
		InputEdges.push_back(x);
		InputEdges.push_back(y);	
	}
	
	ifstream infile_r(file);	
	
	while(infile_r>>user_a>>user_b) {

		if(in_deg.find(user_a)==in_deg.end()) in_deg[user_a]=1;
		else in_deg[user_a]+=1;
		int x=user2ID[user_b];
		int y=user2ID[user_a];
		
		count_edges++;
		InputEdges.push_back(x);
		InputEdges.push_back(y);	
	}	
	
	n=count_vertices;
	m=count_edges;
	
	cout<<"number of users:"<<n<<" number of edges:"<<m<<"\n";
	
	
	//viewpoint
	vector<string>::iterator it_vector;
	
	unsigned seed = std::chrono::system_clock::now().time_since_epoch().count();  
    std::mt19937 gen(seed);  
  
    // 定义在-1到1范围内的均匀实数分布  
    std::uniform_real_distribution<> dis(-1.0, 1.0);  
  
    // 生成随机数  
    
	
	for(it_vector=username.begin();it_vector!=username.end();it_vector++)
	{
		double randomNumber = dis(gen);
		viewpoint[*it_vector]=round(randomNumber * 10) / 10;
	}

	//EdgeProb
	ifstream infile2(file);
	while(infile2>>user_a>>user_b){
		EdgeProb.push_back(1.0/in_deg[user_b]);
	}
	
	ifstream infile3(file);
	while(infile3>>user_a>>user_b){
		EdgeProb.push_back(1.0/in_deg[user_a]);
	}
		
	if(adj_out.size()<n) adj_out.resize(n);
	
	//构造出度邻接表 
	for (int j=0; j<InputEdges.size(); j+=2){
		//edge x -> y
		x = InputEdges.at(j);	 
		y = InputEdges.at(j+1);
		int i=j/2;
		adj_out[x].push_back(pair<int,double>(y,EdgeProb[i]));
	}
	adj_in.resize(n); 
	//构建入度邻接表
	for(int j=0;j<InputEdges.size();j+=2){
		//edge x -> y
		x=InputEdges.at(j);
		y=InputEdges.at(j+1);
		int i=j/2;
		adj_in[y].push_back(pair<int,double>(x,EdgeProb[i])); 
	} 

	
	//userID_Name;
	for(map<string, int>::iterator it_map=user2ID.begin();it_map!=user2ID.end();it_map++){
		userID_Name[it_map->second]=it_map->first;
	}
	
	
	fprintf(stderr, "END reading graph (%s).\n", file); 
	
	

}

void clear(queue<int>& q) {
    queue<int> empty;
    swap(empty, q);
}

void findSpreader(int num_spreader){
	//random select
	int num_harm=num_spreader/20;			
	int num_bene=num_spreader-num_harm;		
	
	vector<string> harmuser;
	vector<string> beneuser;
	map<string,double>::iterator it;
	for(it=viewpoint.begin();it!=viewpoint.end();it++){
		if(fabs(it->second-(-1.0))<1e-6 || fabs(it->second-1.0)<1e-6) harmuser.push_back(it->first);
		else beneuser.push_back(it->first);
	}

  	unsigned seed = std::chrono::system_clock::now().time_since_epoch().count();  
    std::mt19937 gen(seed);  
	std::uniform_int_distribution<> dis_harm(0, harmuser.size() - 1);
	vector<string>::iterator itt;
	
	
	if(harmuser.size()<=num_harm){
		Sh=harmuser;
		num_bene=num_spreader-harmuser.size();
	}
	
	
	else{	

		//select spreaders based on out degree
		
		int visit[n]={0};
		int cnt=0;
		while(cnt<num_harm){
			cnt++;
			double max_out_deg=-1;
			string index="";
			for(vector<string>::iterator it=harmuser.begin();it!=harmuser.end();it++){
				if(visit[user2ID[*it]]==0 && adj_out[user2ID[*it]].size()>max_out_deg){
					max_out_deg=adj_out[user2ID[*it]].size();
					index=*it;
				}
			}
			visit[user2ID[index]]=1;
			Sh.push_back(index);
		}
		 	
	}

	int visit[n]={0};
	int cnt_bene=0;
	while(cnt_bene<num_bene){
		cnt_bene++;
		double max_out_deg=-1;
		string index="";
		for(vector<string>::iterator it=beneuser.begin();it!=beneuser.end();it++){
			if( visit[user2ID[*it]]==0 && adj_out[user2ID[*it]].size()>max_out_deg){
				max_out_deg=adj_out[user2ID[*it]].size();
				index=*it;
			}
		}
		visit[user2ID[index]]=1;
		Sb.push_back(index);
	}
	
	
	//divide S into I subsets
	queue<int> spreader_for_one_view;
	double viewp=-1.00;
	int i=0;
	while(!(viewp>1.00)){
		//-1 or 1 
		if(fabs(viewp-(-1.00))<1e-6 || fabs(viewp-1.00)<1e-6){
			for(itt=Sh.begin();itt!=Sh.end();itt++){
				if( fabs(viewpoint[*itt]-viewp)<1e-6 ) spreader_for_one_view.push(user2ID[*itt]);
			}
		}
		else{
			for(itt=Sb.begin();itt!=Sb.end();itt++){
				if( fabs(viewpoint[*itt]-viewp)<1e-6 ) spreader_for_one_view.push(user2ID[*itt]);
			}			
		}
		spreader[i]=spreader_for_one_view;
		viewp+=0.10;
		i++;
		clear(spreader_for_one_view);
	}
	
}

double EHemptyset(){
	
	set<string> harm_users;
	double influence=0.0;
	int round=10000;
	
	while(round--){
		vector<string> resultlist_r1;	//viewpoint "-1"
		vector<int> checked_r1(n,0);	
		
		for(vector<string>::iterator it_sh=Sh.begin();it_sh!=Sh.end();it_sh++){
			if( fabs(viewpoint[*it_sh]-(-1) )<1e-6 ) resultlist_r1.push_back(*it_sh);
		}
		
		vector<string>::iterator it=resultlist_r1.begin();
		for(;it!=resultlist_r1.end();it++){
			checked_r1[user2ID[*it]]=1;
		}
		
	
		while(resultlist_r1.size()!=0){
			
			string current_node=resultlist_r1.front();
			resultlist_r1.erase(resultlist_r1.begin());
			
			harm_users.insert(current_node);

			//select out-neighbors of the current_node
			for(auto it_list=adj_out[user2ID[current_node]].begin();it_list!=adj_out[user2ID[current_node]].end();it_list++){
				
				double edgepro=(*it_list).second;
				
				string username_v=userID_Name[(*it_list).first];
	
				double nodepro=1.0-fabs(-1.0-viewpoint[username_v])/2;
				
				if(checked_r1[(*it_list).first]==0&&a_rand()<=edgepro*nodepro){
					checked_r1[(*it_list).first]=1;
					resultlist_r1.push_back(username_v);
				}
			}	
		}	
		
		
		
		
		vector<string> resultlist_s1;	// viewpoint "1"
		vector<int> checked_s1(n,0);	
		
		for(vector<string>::iterator it_sh=Sh.begin();it_sh!=Sh.end();it_sh++){
			if( fabs(viewpoint[*it_sh]-1 )<1e-6 ) resultlist_s1.push_back(*it_sh);
		}
		
		
		it=resultlist_s1.begin();
		for(;it!=resultlist_s1.end();it++){
			checked_s1[user2ID[*it]]=1;
		}
		

		while(resultlist_s1.size()!=0){
			
			string current_node=resultlist_s1.front();
			resultlist_s1.erase(resultlist_s1.begin());
			
			harm_users.insert(current_node);
			
			//select out-neighbors of the current_node
			for(auto it_list=adj_out[user2ID[current_node]].begin();it_list!=adj_out[user2ID[current_node]].end();it_list++){
				
				double edgepro=(*it_list).second;
				
				string username_v=userID_Name[(*it_list).first];

				double nodepro=1.0-fabs(1.0-viewpoint[username_v])/2;

				if(checked_s1[(*it_list).first]==0&&a_rand()<=edgepro*nodepro){
					checked_s1[(*it_list).first]=1;
					resultlist_s1.push_back(username_v);
				}
			}	
		}
		
		influence+=(harm_users.size() - Sh.size() );
		harm_users.clear();
	} 
	
	
	return 1.0*influence/10000;
}

map<int, list<int> > generate_live_edge_g(vector<list<pair<int,double> > > & G_d ,  vector<int> & deleted){
	map<int, list<int> > g;
	for(size_t i=0;i<G_d.size();i++){
		if(deleted[i]==1) continue;
		for(auto& pair: G_d[i]){
			if(deleted[pair.first]==0&&a_rand()<=pair.second){
				g[i].push_back(pair.first);
			}	
		}
	}	

	
	return g;
	
}

map<int, list<int> > generate_viewpoint_sampling_graph(map<int, list<int> > & g, double & vie, vector<int> & deleted){
	map<int, list<int> > gj=g;
	int in_del[n]={0};
	//map<string, double> viewpoint;
	
	for(map<string, double>::iterator it=viewpoint.begin();it!=viewpoint.end();it++){
		double nodepro=1.0-fabs(vie-it->second)/2;
		if(a_rand()>nodepro) in_del[user2ID[it->first]]=1;
	}

	
	//Traverse the adjacency table and remove the entry edges of these nodes
	map<int, list<int> >::iterator it;
	for (it=gj.begin(); it != gj.end(); ++it) {    
        for (list<int>::iterator adj=(it->second).begin(); adj!=(it->second).end();) {  
            list<int>::iterator temp=adj++;
			if(in_del[*temp]==1) (it->second).erase(temp);
        }    
    }
    

	
	//map<int, list<int> > gjj;
	int s=-1;	//new point of spreaders of -1
	vector<int> point_to_merge;
	for(vector<string>::iterator itt=Sh.begin();itt!=Sh.end();itt++){
		if( deleted[user2ID[*itt]]==0 && fabs(viewpoint[*itt] - vie)<=1e-6 ){
			point_to_merge.push_back(user2ID[*itt]);
		}
	}
	
	// duplicate removal
    std::unordered_set<int> unique_edges;
    
	// Traverse each node to be merged, add its edge to the edge list of the new node, and remove duplicates
    for (int point : point_to_merge) {  
        if (gj.find(point) != gj.end()) {  
            for (int edge : gj[point]) {  
                // Only add edges when they are not in the emerging edge list of the new node, and ensure that edges inside the merged node are also not added
                if (find(point_to_merge.begin(),point_to_merge.end(),edge)==point_to_merge.end() && unique_edges.find(edge) == unique_edges.end()) { 
				 
                    gj[s].push_back(edge);  
                    unique_edges.insert(edge);  
                }  
            }  
        }  
    }  
    
	
	 // Remove these nodes to be merged from the map 
    for (int point : point_to_merge) {  
        gj.erase(point);  
    }  


	return gj;
}


void BFS_for_nodes(map<int,list<int> >& gj, set<int>& xi_sg_current, vector<int>& nodes_source, vector<pair<int,int> >& edges_source,int start_id){
	queue<int> q;
	q.push(start_id);
	xi_sg_current.insert(start_id);
	nodes_source.push_back(start_id);
	while(!q.empty()){
		int current=q.front();
		q.pop();
		
		for(list<int>::iterator it=gj[current].begin();it!=gj[current].end();it++){
			if(xi_sg_current.find(*it)==xi_sg_current.end()){
				q.push(*it);
				xi_sg_current.insert(*it);
				nodes_source.push_back(*it);
				edges_source.push_back({current, *it});
				
			}
		}
		
	}
	
}



void dfs(int x) {  
    id[++tim] = x;  
    dfn[x] = tim;  
  
    for (int i = G.head[x]; i; i = G.edge[i].next) {  
        int to = G.edge[i].to;  
        if (!dfn[to]) {  
            dfs(to);  
            father[to] = x;  
            dfsTree.addEdge(x, to);  
        }  
    }  
}  


int sdom[N+1];  
int mn[N+1]; // mn[i] represents the smallest ancestor of sdom on the DFS tree of node i, hence sdom [mn [i]]=sdom [i]
int anc[N+1];       // anc [i] represents the ancestor of i  
int find(int x) { //Weighted path compression and query set  
    if (x != anc[x]) {  
        int t = anc[x];  
        anc[x] = find(anc[x]);  
        if (dfn[sdom[mn[x]]] > dfn[sdom[mn[t]]])  
            mn[x] = mn[t];  
    }  
    return anc[x];  
}  
void LengauerTarjan(int nn, int mm) { //find sdom
    for (int i = 1; i <= nn; i++) {  
        anc[i] = i;  
        sdom[i] = i;  
        mn[i] = i;  
    }  
    for (int j = nn; j >= 2; j--) {  
        int x = id[j];  
        if (!x)  
            continue;  
  
        int pos = j;  
        for (int i = GF.head[x]; i; i = GF.edge[i].next) {  
            int y = GF.edge[i].to;  
            if (!dfn[y])  
                continue;  
            if (dfn[y] < dfn[x])  
                pos = min(pos, dfn[y]);  
            else {  
                find(y); //Find an ancestor z on the tree that satisfies dfn [z]>dfn [x] for y
                pos = min(pos, dfn[sdom[mn[y]]]);  
            }  
        }  
        sdom[x] = id[pos];  
        anc[x] = father[x];  
        dfsTree.addEdge(sdom[x], x);   
    }  
}  
  
int deep[N+1], dp[N+1][25];  
int getLCA(int x, int y) {  
    if (deep[x] < deep[y])  
        swap(x, y);  
    int del = deep[x] - deep[y];  
    for (int i = 0; i <= 20; i++)  
        if ((1 << i) & del)  
            x = dp[x][i];  
    if (x == y)  
        return x;  
    for (int i = 20; i >= 0; i--) {  
        if (dp[x][i] != dp[y][i]) {  
            x = dp[x][i];  
            y = dp[y][i];  
        }  
    }  
    return dp[x][0];  
}  
void buildDominate(int x) { //construct dominator tree 
    int to = dfsTreeF.edge[dfsTreeF.head[x]].to;  
    for (int i = dfsTreeF.head[x]; i; i = dfsTreeF.edge[i].next) {  
        int y = dfsTreeF.edge[i].to;  
        to = getLCA(to, y);  
    }  
    deep[x] = deep[to] + 1;  
    dp[x][0] = to;  
    dominate.addEdge(to, x);  
    subtree[x].push_back(x); // add itself to the subtree collection 
  
    for (int i = 1; i <= 20; i++)  
        dp[x][i] = dp[dp[x][i - 1]][i - 1];  
}  
int in[N]; // The in degree of DFS tree  
void topSort(int nn,int mm) {  
    for (int i = 1; i <= nn; i++) {  
        for (int j = dfsTree.head[i]; j; j = dfsTree.edge[j].next) {  
            int to = dfsTree.edge[j].to;  
            in[to]++;  
            dfsTreeF.addEdge(to, i);  
        }  
    }  
    for (int i = 1; i <= nn; i++) {  
        if (!in[i]) {  
            dfsTree.addEdge(0, i);  
            dfsTreeF.addEdge(i, 0); 
        }  
    }  
  
    queue<int> Q;  
    Q.push(0);  
    while (Q.size()) {  
        int x = Q.front();  
        Q.pop();  
        for (int i = dfsTree.head[x]; i; i = dfsTree.edge[i].next) {  
            int y = dfsTree.edge[i].to;  
            if ((--in[y]) <= 0) {  
                Q.push(y);  
                buildDominate(y);  
            }  
        }  
    }  
}  
  
void dfsDominate(int x) { //DFS on the dominating tree to collect subtree nodes
    for (int i = dominate.head[x]; i; i = dominate.edge[i].next) {
		int to = dominate.edge[i].to;
		dfsDominate(to);
		subtree[x].insert(subtree[x].end(), subtree[to].begin(), subtree[to].end());
	}
}

void DTree(int num_node,int num_edge,vector<pair<int,int> >& edges_source_mapping){
	for(int i=0;i<=num_node;i++){
		if(i<N) father[i]=dfn[i]=id[i]=sdom[i]=mn[i]=anc[i]=deep[i]=in[i]=0;
		else sdom[i]=mn[i]=anc[i]=deep[i]=in[i]=0;
		for(int j=0;j<25;j++) dp[i][j]=0;
	}

	G.clear(); GF.clear();             
	dfsTree.clear(); dfsTreeF.clear(); 
	dominate.clear();       
	xx.clear();  
	
	for(int i=0;i<num_edge;i++){
		int x=edges_source_mapping[i].first;
		int y=edges_source_mapping[i].second;
		G.addEdge(x, y);
		GF.addEdge(y, x); 
	}
	
	tim = 0;  
	dfs(1); // Starting from node 1, establish DFS tree
	
	LengauerTarjan(num_node,num_edge); // Lengauer-Tarjan algorithm
	
	topSort(num_node,num_edge); // Topology sorting, while establishing a dominating tree
	
	// Perform DFS on the dominating tree and collect the subtree nodes of each node
	dfsDominate(0); 
	
}


//obtain B_h
void HVB(int budget,double gamma,int round){
	
	
	
	int J=2;
	double vies[2]={-1.0,1.0};
	//compute E[H(\emptyset)]
	infharm=EHemptyset();
	int theta=10000;
	if(fabs(infharm-0)<=1e-6 ){
		return;
	}
	vector<int> zeta_visit(n,0);		//flag
	
	double zeta_in_Bh=0.0;		//sum_result
	vector<int> deleted(n,0);			//flag_delete_in_Bh
	
	vector<list<pair<int,double> > > G_d=adj_out; 
	auto start = std::chrono::high_resolution_clock::now();  	
	while(zeta_in_Bh< (1.0+epsilon)*(1-gamma)*infharm){

		//double* zeta=new double[n];
		//for(int i=0;i<n;i++) zeta[i]=0.0;

		vector<double> zeta(n,0.0);

		for(int i=1;i<=theta;i++){
		
			map<int, list<int> > g = generate_live_edge_g(G_d,deleted);
		
			set<int> xi_sg[2];
			std::vector<std::vector<std::vector<int>>> xi_u_sg(2, std::vector<std::vector<int>>(n));
			
			for(int j=0;j<J;j++){

				map<int, list<int> > gj = generate_viewpoint_sampling_graph(g,vies[j],deleted);

				//\xi(s,g^{o_j})
				vector<int> nodes_source;
				vector<pair<int,int> > edges_source;
				int start_id=-1;
				BFS_for_nodes(gj, xi_sg[j], nodes_source, edges_source,start_id);
				
				//DTree
				//vector<int> nodes_source_mapping;
				vector<pair<int,int> > edges_source_mapping;
				map<int,int> true_vir;
				map<int,int> vir_true;
				
				for(int l=0;l<nodes_source.size();l++){
					true_vir[nodes_source[l]]=l+1;
					vir_true[l+1]=nodes_source[l];
				}
				
				for(vector<pair<int,int> >::iterator it=edges_source.begin();it!=edges_source.end();it++){
					edges_source_mapping.push_back({true_vir[it->first],true_vir[it->second]});
				}
				
				DTree(nodes_source.size(), edges_source_mapping.size() , edges_source_mapping);

				for (int l = 1; l <= nodes_source.size(); l++) {  
				    if(vir_true[l]==-1) continue;
					vector<int>::iterator it;
				    for(it=subtree[l].begin();it!=subtree[l].end();it++){ 
				    
				    	if(find(xi_u_sg[j][vir_true[l]].begin(),xi_u_sg[j][vir_true[l]].end(),*it)==xi_u_sg[j][vir_true[l]].end())
				    		xi_u_sg[j][vir_true[l]].push_back(vir_true[*it]);
					}
				}
	
				for(int l=0;l<=nodes_source.size();l++){
					subtree[l].clear();
				}
				
					
			}
			
			set<int> xi_sg_union;	//contain -1 
			
			set_union(
				xi_sg[0].begin(),xi_sg[0].end(),
				xi_sg[1].begin(),xi_sg[1].end(),
				inserter(xi_sg_union,xi_sg_union.begin())	
			);
			
			int xi_sg_number=xi_sg_union.size()-1; 	

			
			//zeta_u 
			for(const auto &l : xi_sg_union){
				if(l==-1) continue;
				vector<int> temp[2];
				set<int> xi_u_sg_union;
				for(int j=0;j<J;j++){
					temp[j].insert(temp[j].end(),xi_sg[j].begin(),xi_sg[j].end());	//set-> vector
					//delete
					for(vector<int>::iterator it=xi_u_sg[j][l].begin();it!=xi_u_sg[j][l].end();it++){
						auto itt=find(temp[j].begin(),temp[j].end(),*it);
						if(itt!=temp[j].end()){
							temp[j].erase(itt);
						}
					}
					xi_u_sg_union.insert(temp[j].begin(),temp[j].end());
				}
				
				int xi_sg_u_number=xi_u_sg_union.size()-1;
				
				zeta[l]=zeta[l]+(xi_sg_number*1.0-xi_sg_u_number*1.0)/(theta*1.0);
			}
		}
		
		//optimal zeta
		double maxzeta=-1.0;
		int index=-1;
		for(int l=0;l<n;l++){
			if(zeta_visit[l]==0&&maxzeta<zeta[l]){
				maxzeta=zeta[l];
				index=l;
			}
		} 
		zeta_visit[index]=1;
		deleted[index]=1;
		zeta_in_Bh+=maxzeta;
		B_h.insert(index);
		
	}
	cout<<"rate："<<1.0-zeta_in_Bh/infharm<<endl;
	auto end = std::chrono::high_resolution_clock::now();  
	auto duration = std::chrono::duration_cast<std::chrono::milliseconds>(end - start); 
	std::cout << "running time of HVB: " << duration.count() << "ms" << std::endl;
}


double computeDiversityofExposure(set<double> L){
	double gu=0.0;
	int cnt=0;
	double prev=-1.0;
	for(auto it=L.begin();it!=L.end();it++){
		double current=*it;
		double diff=current-prev;
		gu+=pow(diff,2);
		prev=current;
		
	}
	
	gu+=pow(1.0-prev,2);
	
	double fu=1.0-gu/4.0;
	return fu;
	
}


void DBEM2(int budget,int k,int round){
	int litk=budget;		//remaining budget 
	set<int> CP;	
	set<int> CP_upper;
	const int theta=5000;
	int target_node[theta];	//target_node
	for(int i=0;i<theta;i++) target_node[i]=-1;	
	const int vie_num=19;
	double vies[vie_num];	//viewpoints
	for(int i=0;i<vie_num;i++){
		vies[i]=-0.9+i*0.1;
		
	}
	
	unsigned seed = std::chrono::system_clock::now().time_since_epoch().count();  
    std::mt19937 gen(seed);  
    
    std::uniform_int_distribution<> dis(0, n-1);  
	for(int the=0;the<theta;the++){
		target_node[the]=dis(gen);
	}	

	

	vector<vector<vector<int>>> upath(n,vector<std::vector<int>>(theta,vector<int>(vie_num, 0)));
	vector<vector<vector<int>>> spath(n,vector<std::vector<int>>(theta,vector<int>(vie_num, 0)));
	vector<vector<vector<int>>> upath_upper(n,vector<std::vector<int>>(theta,vector<int>(vie_num, 0)));
	
	auto start = std::chrono::high_resolution_clock::now();  		
	for(int i=0;i<theta;i++){
		
		for(int j=0;j<vie_num;j++){
			//r_v= vie
			if( fabs(viewpoint[userID_Name[target_node[i]]] - vies[j] )<=1e-6 ) continue; 
			
			vector<int> v_visit(n,0);
			vector<int> s_visit(n,0);
			//reverse BFS
			queue<int> v;
			v.push(target_node[i]);
			v_visit[target_node[i]]=1;
			while(!v.empty()){
				int current=v.front();
				v.pop();
				int flag=1;	
				if(current!=target_node[i]){
					double nodepro=1.0-fabs(vies[j]-viewpoint[userID_Name[current]])/2.0;
					if(a_rand()<=nodepro){
						flag=1; 
					}
					else flag=0;

				}
					
				if(flag==1){
					
					for(auto elem:adj_in[current]){
						if(a_rand()>elem.second) continue;
						int w=elem.first;
						if(v_visit[w]==1) continue;
						v.push(w);
						upath[w][i][j]=1;
						upath_upper[w][i][j]=1;
						//upath_for_B_b[w][i][j]=1;	
						v_visit[w]=1;					
					}		
						
				}

				
			}
							
			//BFS
			//queue<int> s=spreader[j+1];
			queue<int> s;
			for(vector<string>::iterator it=Sb.begin();it!=Sb.end();it++){
				if( fabs(viewpoint[*it] - vies[j])<=1e-6 ){
					s.push(user2ID[*it]);
					s_visit[user2ID[*it]]=1;
				}
			}
			
			if(s.empty()) continue;
			
			while(!s.empty()){
				int current=s.front();
				s.pop();
				double nodepro=1.0-fabs(vies[j]-viewpoint[userID_Name[current]])/2.0;
				int flag=0; 

				if(a_rand()<=nodepro){
					flag=1;
				}
				
				if(flag==1){
					for(auto elem:adj_out[current]){
						if(a_rand()>elem.second) continue;
						int w=elem.first;
						if(s_visit[w]==1) continue;
						s.push(w);
						spath[w][i][j]=1;
						s_visit[w]=1;					
					}	
					
				}
				
				
			}
			
			
			if(spath[target_node[i]][i][j]==1){
				continue;
			}
				

			
			for(int l=0;l<n;l++){
				if(upath_upper[l][i][j]==1) CP_upper.insert(l);
				if(spath[l][i][j]==1&&upath[l][i][j]==1){
					CP.insert(l);
				}
			}
			

		}
		
	}


	
	cout<<CP_upper.size()<<"CP size"<<CP.size()<<endl;
	
	
	//first compute \phi(\emptyset)

	vector<std::set<double>> target_node_view(theta);  
	vector<std::set<double>> target_node_view_lower(theta);  
	vector<std::set<double>> target_node_view_upper(theta);  
	vector<std::set<double>> target_node_view_upper_new(theta);
	vector<std::set<double>> target_node_view_B_b_new(theta);
	double phi_empty=0.0;
	for(int i=0;i<theta;i++){
		target_node_view[i].insert(viewpoint[userID_Name[target_node[i]]]);
		for(int j=0;j<vie_num;j++){
			if(spath[target_node[i]][i][j]==1) target_node_view[i].insert(vies[j]);
			
		}
		
		phi_empty+=computeDiversityofExposure(target_node_view[i]);
		
	}
	
	phi_empty=phi_empty*n/theta;
	cout<<"Minimum："<<phi_empty/n<<endl;
	
	int budget_lower=budget;
	int budget_upper=budget;

	for(int i=0;i<theta;i++){
		target_node_view_B_b_new[i]=target_node_view_upper_new[i]=target_node_view_lower[i]=target_node_view_upper[i]=target_node_view[i];
		
	}


	set<int> CP_lower=CP;
	//lowerbound
	double phi_lower_bound=phi_empty;
	
	vector<int> deleted_lower(n,0);
	while(B_b_lower.size()<budget_lower){
		if(CP_lower.size()==0){
			int rannode=dis(gen);
			while(deleted_lower[rannode]==1){
				rannode=dis(gen);
			}
			CP_lower.insert(rannode);
			CP.insert(rannode);
			
		}
		int index=-1;
		double maxdeltaDE=-1;	
		int vieset[vie_num]={0};	
		for(auto&elem:CP_lower){
			double deltaDE=0.0; 
			for(int i=0;i<theta;i++){
				set<double> temp=target_node_view_lower[i];
				for(int j=0;j<vie_num;j++){
					if(spath[target_node[i]][i][j]==0 && spath[elem][i][j]==1 && upath[elem][i][j]==1){
						temp.insert(vies[j]);
					}
				}
				//dbe
				deltaDE+=computeDiversityofExposure(temp)-computeDiversityofExposure(target_node_view_lower[i]);
				
			}
			
			if(deltaDE>maxdeltaDE){
				maxdeltaDE=deltaDE;
				index=elem;				
			}
			
		}
		
		
		
		phi_lower_bound+=maxdeltaDE*n/theta;
		
		CP_lower.erase(index);
		
		B_b_lower.insert(index);		
		
		if(B_h.find(index)!=B_h.end()) budget_lower=budget_lower+1;			
	} 

	//+ B_h
	for(auto& elem:B_h){
		for(int i=0;i<theta;i++){
			set<double> temp=target_node_view_lower[i];
			for(int j=0;j<vie_num;j++){
				if(spath[target_node[i]][i][j]==0 && spath[elem][i][j]==1 && upath[elem][i][j]==1){
					temp.insert(vies[j]);
				}
			}
			phi_lower_bound+=(computeDiversityofExposure(temp)-computeDiversityofExposure(target_node_view_lower[i]) )*n/theta;
			
			target_node_view_lower[i]=temp;					
		}
		
	}

	cout<<"lower bound："<<phi_lower_bound/n<<endl;


	//上界 
	double phi_upper_bound=phi_empty;
	
	while(B_b_upper.size()<budget_upper){
		
		int index=-1;
		double maxdeltaDE=-1;	
		int vieset[vie_num]={0};	 
		for(auto&elem:CP_upper){
			double deltaDE=0.0; 
			for(int i=0;i<theta;i++){
				set<double> temp=target_node_view_upper[i];
				for(int j=0;j<vie_num;j++){
					if(spath[target_node[i]][i][j]==0 && upath_upper[elem][i][j]==1){
						temp.insert(vies[j]);
					}
				}
				//dbe
				deltaDE+=computeDiversityofExposure(temp)-computeDiversityofExposure(target_node_view_upper[i]);
				
			}
			
			if(deltaDE>maxdeltaDE){
				maxdeltaDE=deltaDE;
				index=elem;				
			}
			
		}
		
		for(int i=0;i<theta;i++){
			set<double> temp=target_node_view_upper[i];
			for(int j=0;j<vie_num;j++){
				if(spath[target_node[i]][i][j]==0 && upath_upper[index][i][j]==1){
					temp.insert(vies[j]);
				}
			}
			target_node_view_upper[i]=temp;					
		}	
		
			
		
		phi_upper_bound+=maxdeltaDE*n/theta;
		
		
		B_b_upper.insert(index);		
		
		//update CP_upper
		CP_upper.erase(index);
		
		if(B_h.find(index)!=B_h.end()) budget_upper=budget_upper+1;	
	} 	
	
	double upper_before_bh=phi_upper_bound;
	//+ B_h
	for(auto& elem:B_h){
		for(int i=0;i<theta;i++){
			set<double> temp=target_node_view_upper[i];
			for(int j=0;j<vie_num;j++){
				if(spath[target_node[i]][i][j]==0 && spath[elem][i][j]==1 && upath[elem][i][j]==1){
					temp.insert(vies[j]);
				}
			}
			phi_upper_bound+=(computeDiversityofExposure(temp)-computeDiversityofExposure(target_node_view_upper[i]) )*n/theta;
			
			target_node_view_upper[i]=temp;					
		}
		
	}	
	
	
	cout<<"upper bound："<<phi_upper_bound/n<<endl;
	
	
	vector<int> visited_B_b(n,0); 
	
	double phi=phi_empty;	//result
		
	while(B_b.size()<budget){
		int index=-1;
		double maxdeltaDE=-1;	
		int vieset[vie_num]={0};	
		for(auto&elem:CP){
			double deltaDE=0.0; 
			for(int i=0;i<theta;i++){
				set<double> temp=target_node_view[i];
				for(int j=0;j<vie_num;j++){
					if(spath[target_node[i]][i][j]==0 && spath[elem][i][j]==1 && upath[elem][i][j]==1){
						temp.insert(vies[j]);
					}
				}
				//dbe
				deltaDE+=computeDiversityofExposure(temp)-computeDiversityofExposure(target_node_view[i]);
				
			}
			
			if(deltaDE>maxdeltaDE){
				maxdeltaDE=deltaDE;
				index=elem;				
			}
			
		}
		
		for(int i=0;i<theta;i++){
			set<double> temp=target_node_view[i];
			for(int j=0;j<vie_num;j++){
				if(spath[target_node[i]][i][j]==0 && spath[index][i][j]==1 && upath[index][i][j]==1){
					temp.insert(vies[j]);
				}
			}
			target_node_view[i]=temp;					
		}		
		
		phi+=maxdeltaDE*n/theta;
		
		
		B_b.insert(index);
		
		visited_B_b[index]=1;
		
		//update CP 
		CP.erase(index);
		
		for(int i=0;i<theta;i++){
			
			for(int j=0;j<vie_num;j++){
			
				if(spath[target_node[i]][i][j]==1){
					continue;
				}
				//reverse update from node index
				int v_visit[n]={0};
				//reverse BFS
				queue<int> v;
				v.push(target_node[i]);
				v_visit[target_node[i]]=1;
				while(!v.empty()){
					int current=v.front();
					v.pop();
					int flag=1;	 
					if(current!=target_node[i]){
						double nodepro=1.0-fabs(vies[j]-viewpoint[userID_Name[current]])/2.0;
						if(a_rand()<=nodepro){
							flag=1;
						}
						else flag=0;
						
					}
					if(visited_B_b[current]==1){
						flag=1;
					}
						
					if(flag==1){
				
						for(auto elem:adj_in[current]){
							int w=elem.first;
							if(a_rand()>elem.second) continue;
							if(v_visit[w]==1) continue;
							v.push(w);
							upath[w][i][j]=1;
							v_visit[w]=1;
							if(spath[w][i][j]==1&&upath[w][i][j]==1) {
								double nodepro=1.0-fabs(vies[j]-viewpoint[userID_Name[w]])/2.0;
								if(a_rand()<=nodepro){
									CP.insert(w);	
								}
							}				
						}					
								
					}
	
					
				}
								
			
				
			}
			
		}
		 
		
		if(B_h.find(index)!=B_h.end()) {
			budget=budget+1;
		}
	}

	cout<<"beforebh:"<<phi/n<<endl; 
	//double beforebh=phi/n;
	//+B_h
	
	double phi_sep=phi; 
	
	for(auto& elem:B_h){
		for(int i=0;i<theta;i++){
			set<double> temp=target_node_view[i];
			for(int j=0;j<vie_num;j++){
				if(spath[target_node[i]][i][j]==0 && spath[elem][i][j]==1 && upath[elem][i][j]==1){
					temp.insert(vies[j]);
				}
			}
			phi+=(computeDiversityofExposure(temp)-computeDiversityofExposure(target_node_view[i]) )*n/theta;
			
			target_node_view[i]=temp;					
		}
		
	}
	cout<<"Obj func："<<phi/n<<endl;
	
	
	auto end = std::chrono::high_resolution_clock::now(); 
	auto duration = std::chrono::duration_cast<std::chrono::milliseconds>(end - start);  
	cout << "running time of DBEM: " << duration.count() << "ms" << std::endl;

}




void HGA(int budget, int num_spreader, double gamma, int round){
	
	HVB(budget,gamma,round); //obtain B_h
	
	DBEM2(budget-B_h.size(),budget,round); //obtain B_b
	 
}


int main(){


	const char *file="iphone_samsung\\iphone_samsung_network_heterogeneous.txt";
	//const char *file="brexit\\brexit_network_heterogeneous.txt";
	//const char *file="uselections\\uselections_network_heterogeneous.txt";
	//const char *file="facebook_combined.txt\\facebook_combined.txt";
	//const char *file="cit-HepTh.txt\\cit-HepTh.txt";
	
	std::string folder(file);
	size_t pos = folder.find('\\');
	std::string beforeSlash = folder.substr(0, pos);
	
	if(beforeSlash=="cit-HepTh.txt"){
		readGraph2(file); 
	} 
	else if(beforeSlash=="facebook_combined.txt"){
		readGraph3(file);
	}
	else readGraph(file);
	
	//readGraph(file);
	
	int round=0;
	int NUM_TO_SELECT=20;
	int num_spreader=20;
	double gamma=0.7;
	
	while(round<5){
		infharm=0.0;
		Sh.clear();	
		Sb.clear();
		spreader.clear();
		B_h.clear();
		B_b.clear();
		B_f.clear();
		B_b_lower.clear();
		B_b_upper.clear();
		findSpreader(num_spreader);
		HGA(NUM_TO_SELECT, num_spreader, gamma,round);	
		NUM_TO_SELECT+=10; 
		round++;
	}
	cout<<"--------------------------------------"<<endl;


    return 0;
}

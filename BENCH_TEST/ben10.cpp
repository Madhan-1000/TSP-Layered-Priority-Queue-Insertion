// bench_2opt.cpp
// Single-file benchmark: LPQI + other heuristics + 2-opt, CSVs + final_summary.txt
// Compile: g++ -O2 -std=c++17 bench_2opt.cpp -o bench_2opt

#include <bits/stdc++.h>
#include <filesystem>
using namespace std;
namespace fs = std::filesystem;
using steady = chrono::steady_clock;

struct Point { double x,y; };
static double pdist(const Point&a,const Point&b){ return hypot(a.x-b.x,a.y-b.y); }

// ---------------- convex hull (monotone chain)
static vector<int> convex_hull(const vector<Point>& P){
    int n=P.size(); vector<int> ids(n);
    iota(ids.begin(), ids.end(), 0);
    sort(ids.begin(), ids.end(), [&](int a,int b){
        if (P[a].x!=P[b].x) return P[a].x < P[b].x;
        return P[a].y < P[b].y;
    });
    if(n<=1) return ids;
    vector<int> H(2*n); int k=0;
    auto cross=[&](int i,int j,int k2)->double{
        const Point &A=P[i], &B=P[j], &C=P[k2];
        return (B.x-A.x)*(C.y-A.y) - (B.y-A.y)*(C.x-A.x);
    };
    for(int id: ids){
        while(k>=2 && cross(H[k-2],H[k-1],id) <= 0) --k;
        H[k++]=id;
    }
    int t=k+1;
    for(int i=(int)ids.size()-2;i>=0;--i){
        int id=ids[i];
        while(k>=t && cross(H[k-2],H[k-1],id) <= 0) --k;
        H[k++]=id;
    }
    H.resize(max(0,k-1));
    // unique
    vector<int> out; out.reserve(H.size());
    unordered_set<int> seen;
    for(int v: H) if(!seen.count(v)){ out.push_back(v); seen.insert(v); }
    return out;
}

// ---------------- point->segment distance
static double pt_seg_dist(const Point& p, const Point& a, const Point& b){
    double vx=b.x-a.x, vy=b.y-a.y;
    double wx=p.x-a.x, wy=p.y-a.y;
    double denom = vx*vx + vy*vy;
    if(denom==0) return pdist(p,a);
    double t = (wx*vx + wy*vy) / denom;
    if(t<=0) return pdist(p,a);
    if(t>=1) return pdist(p,b);
    Point proj{ a.x + t*vx, a.y + t*vy };
    return pdist(p, proj);
}

// ---------------- 2-opt
static void two_opt_improve(const vector<Point>& P, vector<int>& tour, int max_passes=50){
    int n = tour.size();
    if(n<4) return;
    bool improved=true; int passes=0;
    while(improved && passes<max_passes){
        improved=false; ++passes;
        for(int i=0;i<n-1;++i){
            for(int j=i+2;j<n;++j){
                if(i==0 && j==n-1) continue;
                int a=tour[i], b=tour[(i+1)%n];
                int c=tour[j], d=tour[(j+1)%n];
                double before = pdist(P[a],P[b]) + pdist(P[c],P[d]);
                double after  = pdist(P[a],P[c]) + pdist(P[b],P[d]);
                if(after + 1e-12 < before){
                    reverse(tour.begin()+i+1, tour.begin()+j+1);
                    improved=true;
                }
            }
        }
    }
}

// ---------------- heuristics
static vector<int> NN(const vector<Point>& P){
    int n=P.size(); if(n==0) return {};
    vector<int> tour; tour.reserve(n);
    vector<char> used(n,0);
    int cur = 0; tour.push_back(cur); used[cur]=1;
    for(int k=1;k<n;++k){
        int best=-1; double bd=1e18;
        for(int i=0;i<n;++i) if(!used[i]){
            double d=pdist(P[cur],P[i]);
            if(d<bd){ bd=d; best=i; }
        }
        cur=best; tour.push_back(cur); used[cur]=1;
    }
    return tour;
}

static vector<int> Cheapest(const vector<Point>& P){
    int n=P.size(); if(n==0) return {};
    if(n==1) return {0};
    vector<int> tour = {0,1};
    vector<char> in(n,0); in[0]=in[1]=1;
    while((int)tour.size()<n){
        int bestp=-1, bestpos=0; double bestinc=1e18;
        for(int p=0;p<n;++p) if(!in[p]){
            for(int i=0;i<(int)tour.size();++i){
                int a=tour[i], b=tour[(i+1)%tour.size()];
                double inc = pdist(P[a],P[p]) + pdist(P[p],P[b]) - pdist(P[a],P[b]);
                if(inc < bestinc){ bestinc=inc; bestp=p; bestpos=i+1; }
            }
        }
        tour.insert(tour.begin()+bestpos, bestp); in[bestp]=1;
    }
    return tour;
}

static vector<int> Farthest(const vector<Point>& P){
    int n=P.size(); if(n==0) return {};
    if(n==1) return {0};
    int a=0,b=1; double md=-1;
    for(int i=0;i<n;i++) for(int j=i+1;j<n;j++){
        double d=pdist(P[i],P[j]);
        if(d>md){ md=d; a=i; b=j; }
    }
    vector<int> tour = {a,b};
    vector<char> in(n,0); in[a]=in[b]=1;
    while((int)tour.size()<n){
        int pick=-1; double bestd=-1;
        for(int i=0;i<n;++i) if(!in[i]){
            double mind=1e18;
            for(int v: tour) mind = min(mind, pdist(P[i], P[v]));
            if(mind>bestd){ bestd=mind; pick=i; }
        }
        int bestpos=0; double bestinc=1e18;
        for(int i=0;i<(int)tour.size();++i){
            int u=tour[i], v=tour[(i+1)%tour.size()];
            double inc = pdist(P[u],P[pick]) + pdist(P[pick],P[v]) - pdist(P[u],P[v]);
            if(inc < bestinc){ bestinc=inc; bestpos=i+1; }
        }
        tour.insert(tour.begin()+bestpos, pick); in[pick]=1;
    }
    return tour;
}

static vector<int> MSTdouble(const vector<Point>& P){
    int n=P.size(); if(n==0) return {};
    vector<char> used(n,0);
    vector<double> key(n,1e18);
    vector<int> parent(n,-1);
    key[0]=0;
    for(int iter=0; iter<n; ++iter){
        int u=-1; double best=1e18;
        for(int i=0;i<n;++i) if(!used[i] && key[i]<best){ best=key[i]; u=i; }
        if(u==-1) break;
        used[u]=1;
        for(int v=0; v<n; ++v) if(!used[v]){
            double d=pdist(P[u],P[v]);
            if(d<key[v]){ key[v]=d; parent[v]=u; }
        }
    }
    vector<vector<int>> adj(n);
    for(int v=1; v<n; ++v) if(parent[v]>=0){
        adj[v].push_back(parent[v]); adj[parent[v]].push_back(v);
    }
    vector<int> tour; tour.reserve(n);
    vector<char> vis(n,0);
    function<void(int)> dfs = [&](int u){
        vis[u]=1; tour.push_back(u);
        for(int w: adj[u]) if(!vis[w]) dfs(w);
    };
    dfs(0);
    if((int)tour.size()<n){ for(int i=0;i<n;++i) if(!vis[i]) dfs(i); }
    return tour;
}

// ---------------- LPQI (single-layer PQ insertion)
static vector<int> LPQI(const vector<Point>& Pin){
    int n = Pin.size(); if(n==0) return {};
    vector<Point> P = Pin; // local copy
    vector<int> T = convex_hull(P);
    unordered_set<int> inT(T.begin(), T.end());
    vector<int> rem; rem.reserve(n);
    for(int i=0;i<n;++i) if(!inT.count(i)) rem.push_back(i);

    struct Node{ double d; int p; int stamp; };
    struct Cmp{ bool operator()(const Node&a,const Node&b) const {
        if(a.d!=b.d) return a.d > b.d; return a.stamp > b.stamp;
    }};
    priority_queue<Node, vector<Node>, Cmp> pq;
    int stamp=0;
    for(int pid: rem){
        double best=1e18;
        for(int i=0;i<(int)T.size();++i){
            int a=T[i], b=T[(i+1)%T.size()];
            best = min(best, pt_seg_dist(P[pid], P[a], P[b]));
        }
        pq.push({best, pid, stamp++});
    }
    vector<char> inserted(n,0);
    while(!pq.empty()){
        Node cur = pq.top(); pq.pop();
        if(inserted[cur.p]) continue;
        double best=1e18; int bestidx=0;
        for(int i=0;i<(int)T.size();++i){
            int a=T[i], b=T[(i+1)%T.size()];
            double d = pt_seg_dist(P[cur.p], P[a], P[b]);
            if(d<best){ best=d; bestidx=i; }
        }
        if(fabs(best - cur.d) > 1e-12){
            pq.push({best, cur.p, stamp++});
            continue;
        }
        T.insert(T.begin()+bestidx+1, cur.p);
        inserted[cur.p]=1;
    }
    return T;
}

// ---------------- helper: tour length
static double tour_len(const vector<Point>& P, const vector<int>& tour){
    if(tour.empty()) return 0;
    double L=0; int n=tour.size();
    for(int i=0;i<n;i++) L += pdist(P[tour[i]], P[tour[(i+1)%n]]);
    return L;
}

// ---------------- data generators
static vector<Point> gen_uniform(int N, mt19937_64& rng){
    uniform_real_distribution<double> U(0.0,1.0);
    vector<Point> P; P.reserve(N);
    for(int i=0;i<N;++i) P.push_back({U(rng), U(rng)});
    return P;
}
static vector<Point> gen_clustered(int N, mt19937_64& rng){
    uniform_real_distribution<double> U(0.0,1.0);
    normal_distribution<double> G(0.0, 0.03);
    int k = max(2, min(8, N/20));
    vector<Point> centers; centers.reserve(k);
    for(int i=0;i<k;++i) centers.push_back({U(rng), U(rng)});
    vector<Point> P; P.reserve(N);
    for(int i=0;i<N;++i){
        int c = rng()%k;
        double x = centers[c].x + G(rng);
        double y = centers[c].y + G(rng);
        x = min(1.0, max(0.0, x)); y = min(1.0, max(0.0, y));
        P.push_back({x,y});
    }
    return P;
}

// ---------------- utils: mean,std
static double mean(const vector<double>& a){ if(a.empty()) return 0; double s=0; for(double v:a) s+=v; return s/a.size(); }
static double stddev(const vector<double>& a){ if(a.size()<=1) return 0; double m=mean(a), s=0; for(double v:a) s+=(v-m)*(v-m); return sqrt(s/(a.size()-1)); }

// ---------------- run single trial: run each algorithm, apply 2-opt, write CSV
int main(int argc, char** argv){
    int TRIALS = 10;
    unsigned long long SEED = 123456ULL;
    if(argc>=2) TRIALS = atoi(argv[1]);
    if(argc>=3) SEED = strtoull(argv[2], nullptr, 10);

    vector<int> Ns = {10,20,50,100,200,300,500,1000,1500,2000};
    vector<pair<string,function<vector<int>(const vector<Point>&)>>> algos = {
        {"LPQI", LPQI},
        {"Nearest", NN},
        {"Cheapest", Cheapest},
        {"Farthest", Farthest},
        {"MSTdouble", MSTdouble}
    };

    vector<string> dists = {"uniform", "clustered"};
    mt19937_64 rng(SEED);

    fs::create_directories("output");
    ofstream final("output/final_summary.txt");
    final << "Benchmark summary (2-opt applied after each init). Trials=" << TRIALS << " Seed=" << SEED << "\n\n";

    for(const string& dist : dists){
        for(int N : Ns){
            string base = "output/" + dist + "/N_" + to_string(N);
            fs::create_directories(base);
            final << "Summary for " << dist << " N=" << N << "\n";
            final << "Trials: " << TRIALS << "\n\n";
            final << "Algorithm, mean_runtime_ms, std_runtime_ms, mean_length, std_length, wins\n";

            map<string, vector<double>> runtimes, lengths;
            map<string,int> wins;
            for(auto &p: algos){ runtimes[p.first]=vector<double>(); lengths[p.first]=vector<double>(); wins[p.first]=0; }

            for(int t=0;t<TRIALS;++t){
                vector<Point> P = (dist=="uniform") ? gen_uniform(N,rng) : gen_clustered(N,rng);
                // per-trial storage
                vector<pair<string, pair<double,double>>> trial_rows; // name -> (time_ms, length)
                // for each algo
                for(auto &alg: algos){
                    auto start = steady::now();
                    vector<int> tour = alg.second(P);
                    // run 2-opt
                    two_opt_improve(P, tour, 50);
                    auto end = steady::now();
                    double ms = chrono::duration<double, milli>(end - start).count();
                    double L = tour_len(P, tour);
                    runtimes[alg.first].push_back(ms);
                    lengths[alg.first].push_back(L);
                    trial_rows.push_back({alg.first, {ms,L}});
                }
                // find best length for this trial
                double best = 1e300; for(auto &r: trial_rows) best = min(best, r.second.second);
                for(auto &r: trial_rows) if(fabs(r.second.second - best) < 1e-12) wins[r.first]++;

                // write per-trial CSV
                char csvname[512]; sprintf(csvname, "%s/trial_%02d.csv", base.c_str(), t+1);
                ofstream fout(csvname);
                fout << "algorithm,runtime_ms,length\n";
                for(auto &r: trial_rows) fout << r.first << "," << r.second.first << "," << r.second.second << "\n";
                fout.close();
            } // trials

            // write aggregated summary for this N/dist to final and separate file
            for(auto &alg: algos){
                string name = alg.first;
                double mrt = mean(runtimes[name]), srt = stddev(runtimes[name]);
                double mlen = mean(lengths[name]), slen = stddev(lengths[name]);
                final << name << ", " << mrt << ", " << srt << ", " << mlen << ", " << slen << ", " << wins[name] << "\n";
            }
            final << "\n\n";
            // flush intermediate file too
            cout << "Completed " << dist << " N=" << N << "\n";
        }
    }

    final.close();
    cout << "All done. final_summary written to output/final_summary.txt\n";
    return 0;
}

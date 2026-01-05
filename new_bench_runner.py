import os, math, time, csv, re, random

ROOT = os.path.dirname(os.path.abspath(__file__))
DATA_DIR = os.path.join(ROOT, "TSPLIB95", "CONCORODE_solved_instances")
OUT_DIR = os.path.join(ROOT, "results_stable")
os.makedirs(OUT_DIR, exist_ok=True)

ROTATION_ANGLES = [0, 90]
LK_ITERS = 150
THREE_OPT_LIMIT = 150

# ---------- utils ----------

def dist(a,b): return math.hypot(a[0]-b[0], a[1]-b[1])

def tour_length(t,pts):
    return sum(dist(pts[t[i]],pts[t[(i+1)%len(t)]]) for i in range(len(t)))

def pct_gap(L,opt): return None if opt is None else (L-opt)/opt*100

# ---------- parser ----------

def parse_tsp(path):
    pts,opt=[],None
    with open(path) as f:
        for line in f:
            if "Optimal tour length" in line:
                opt=float(re.search(r"([\d.]+)",line).group(1))
            if line.strip()=="NODE_COORD_SECTION":
                break
        for line in f:
            if line.strip()=="EOF": break
            _,x,y=line.split()
            pts.append((float(x),float(y)))
    return pts,opt

# ---------- geometry ----------

def cross(o,a,b):
    return (a[0]-o[0])*(b[1]-o[1])-(a[1]-o[1])*(b[0]-o[0])

def convex_hull(pts):
    idx=sorted(range(len(pts)),key=lambda i:pts[i])
    if len(idx)<=2: return idx
    lo,up=[],[]
    for i in idx:
        while len(lo)>=2 and cross(pts[lo[-2]],pts[lo[-1]],pts[i])<=0: lo.pop()
        lo.append(i)
    for i in reversed(idx):
        while len(up)>=2 and cross(pts[up[-2]],pts[up[-1]],pts[i])<=0: up.pop()
        up.append(i)
    return lo[:-1]+up[:-1]

# ---------- heuristics ----------

def cheapest_insert(t,p,pts):
    bi,bc=0,1e18
    for i in range(len(t)):
        a,b=t[i],t[(i+1)%len(t)]
        c=dist(pts[a],pts[p])+dist(pts[p],pts[b])-dist(pts[a],pts[b])
        if c<bc: bi,bc=i+1,c
    t.insert(bi,p)

def lpqi(pts):
    hull=convex_hull(pts)
    t=hull[:]
    rem=set(range(len(pts)))-set(hull)
    while rem:
        p=min(rem,key=lambda x:min(
            dist(pts[t[i]],pts[x])+dist(pts[x],pts[t[(i+1)%len(t)]])
            for i in range(len(t))
        ))
        cheapest_insert(t,p,pts)
        rem.remove(p)
    return t

def mhlpqi(pts):
    rem=list(range(len(pts))); t=[]
    while rem:
        sub=[pts[i] for i in rem]
        hull=[rem[i] for i in convex_hull(sub)]
        if not t: t=hull[:]
        else:
            for p in hull: cheapest_insert(t,p,pts)
        rem=[i for i in rem if i not in hull]
    return t

def hull_rot_lpqi(pts):
    best,bL=None,1e18
    for a in ROTATION_ANGLES:
        r=math.radians(a);c,s=math.cos(r),math.sin(r)
        rp=[(c*x-s*y,s*x+c*y) for x,y in pts]
        t=lpqi(rp)
        L=tour_length(t,pts)
        if L<bL: best,bL=t,L
    return best

# ---------- local search ----------

def two_opt(t,pts):
    n=len(t); imp=True
    while imp:
        imp=False
        for i in range(n-2):
            for j in range(i+2,n):
                a,b,c,d=t[i],t[i+1],t[j],t[(j+1)%n]
                if dist(pts[a],pts[b])+dist(pts[c],pts[d]) > \
                   dist(pts[a],pts[c])+dist(pts[b],pts[d]):
                    t[i+1:j+1]=reversed(t[i+1:j+1]); imp=True
    return t

def three_opt(t,pts):
    n=len(t)
    for i in range(n-5):
        for j in range(i+2,n-3):
            for k in range(j+2,n-1):
                a,b,c,d,e,f=t[i],t[i+1],t[j],t[j+1],t[k],t[(k+1)%n]
                if dist(pts[a],pts[b])+dist(pts[c],pts[d])+dist(pts[e],pts[f]) > \
                   dist(pts[a],pts[c])+dist(pts[b],pts[e])+dist(pts[d],pts[f]):
                    t[i+1:j+1]=reversed(t[i+1:j+1])
                    t[j+1:k+1]=reversed(t[j+1:k+1])
    return t

def lk_light(t,pts,iters=LK_ITERS):
    best=tour_length(t,pts)
    t0=time.perf_counter()
    for _ in range(iters):
        i,j=sorted(random.sample(range(len(t)),2))
        t[i:j]=reversed(t[i:j])
        L=tour_length(t,pts)
        if L<best: best=L
        else: t[i:j]=reversed(t[i:j])
    return best,time.perf_counter()-t0

# ---------- bench ----------

def run():
    rows=[]
    for f in os.listdir(DATA_DIR):
        if not f.endswith(".tsp"): continue
        pts,opt=parse_tsp(os.path.join(DATA_DIR,f))
        n=len(pts)
        print(f"\n▶ {f} n={n}")
        for name,algo in [("LPQI",lpqi),("MHLPQI",mhlpqi),("HullRot",hull_rot_lpqi)]:
            print("  ",name)
            t0=time.perf_counter()
            t=algo(pts)
            t1=time.perf_counter()
            t=two_opt(t,pts)
            if n<=THREE_OPT_LIMIT: t=three_opt(t,pts)
            L,t_lk=lk_light(t,pts)
            rows.append([f,n,name,L,pct_gap(L,opt),t1-t0,t_lk])
    out=os.path.join(OUT_DIR,"bench.csv")
    with open(out,"w",newline="") as f:
        csv.writer(f).writerows(
            [["inst","n","alg","len","gap","init_t","lk_t"]]+rows
        )
    print("\n✅ DONE →",out)

if __name__=="__main__":
    run()

import os
import math
import time
import random
import re

# ================= CONFIG =================
ROTATION_ANGLES = [0, 15, 30, 45, 60, 75, 90]
LK_ITERS = 150
THREE_OPT_LIMIT = 150  # skip 3-opt for very large instances

# ================= UTIL =================
def dist(a, b):
    return math.hypot(a[0]-b[0], a[1]-b[1])

def tour_length(tour, pts):
    return sum(dist(pts[tour[i]], pts[tour[(i+1)%len(tour)]]) for i in range(len(tour)))

def pct_gap(L, opt):
    return None if opt is None else (L-opt)/opt*100

# ================= PARSER =================
def parse_tsp(path):
    pts, opt = [], None
    with open(path) as f:
        for line in f:
            if "Optimal tour length" in line:
                m = re.search(r"([\d.]+)", line)
                if m: opt = float(m.group(1))
            if line.strip() == "NODE_COORD_SECTION":
                break
        for line in f:
            if line.strip() == "EOF": break
            _, x, y = line.split()
            pts.append((float(x), float(y)))
    return pts, opt

# ================= GEOMETRY =================
def cross(o,a,b):
    return (a[0]-o[0])*(b[1]-o[1])-(a[1]-o[1])*(b[0]-o[0])

def convex_hull(points):
    idx = sorted(range(len(points)), key=lambda i: points[i])
    if len(idx) <= 2: return idx
    lower, upper = [], []
    for i in idx:
        while len(lower) >= 2 and cross(points[lower[-2]], points[lower[-1]], points[i]) <= 0:
            lower.pop()
        lower.append(i)
    for i in reversed(idx):
        while len(upper) >= 2 and cross(points[upper[-2]], points[upper[-1]], points[i]) <= 0:
            upper.pop()
        upper.append(i)
    return lower[:-1]+upper[:-1]

# ================= INSERTION =================
def cheapest_insertion(tour, idx, pts):
    best_pos, best_cost = 0, float("inf")
    for i in range(len(tour)):
        a, b = tour[i], tour[(i+1)%len(tour)]
        cost = dist(pts[a], pts[idx]) + dist(pts[idx], pts[b]) - dist(pts[a], pts[b])
        if cost < best_cost:
            best_cost, best_pos = cost, i+1
    tour.insert(best_pos, idx)

# ================= HEURISTICS =================
def lpqi(points):
    n = len(points)
    hull = convex_hull(points)
    tour = hull[:]
    remaining = set(range(n)) - set(hull)
    while remaining:
        best_p, best_cost, best_pos = None, float("inf"), None
        for p in remaining:
            for i in range(len(tour)):
                a, b = tour[i], tour[(i+1)%len(tour)]
                cost = dist(points[a], points[p]) + dist(points[p], points[b]) - dist(points[a], points[b])
                if cost < best_cost:
                    best_cost, best_p, best_pos = cost, p, i+1
        tour.insert(best_pos, best_p)
        remaining.remove(best_p)
    return tour

def mhlpqi(points):
    remaining = list(range(len(points)))
    tour = []
    while remaining:
        sub_points = [points[i] for i in remaining]
        hull_idx = convex_hull(sub_points)
        hull = [remaining[i] for i in hull_idx]
        if not tour:
            tour = hull[:]
        else:
            for p in hull:
                cheapest_insertion(tour, p, points)
        remaining = [i for i in remaining if i not in hull]
    return tour

def rotate(points, angle):
    rad = math.radians(angle)
    c,s = math.cos(rad), math.sin(rad)
    return [(c*x - s*y, s*x + c*y) for x,y in points]

def hull_rotation_lpqi(points):
    best_len = float("inf")
    best_tour = None
    for angle in ROTATION_ANGLES:
        rp = rotate(points, angle)
        tour = lpqi(rp)
        L = tour_length(tour, points)
        if L < best_len:
            best_len, best_tour = L, tour
    return best_tour

# ================= LOCAL SEARCH =================
def two_opt(tour, pts):
    improved = True
    while improved:
        improved = False
        n = len(tour)
        for i in range(n-2):
            for j in range(i+2, n):
                a,b,c,d = tour[i], tour[i+1], tour[j], tour[(j+1)%n]
                if dist(pts[a], pts[b])+dist(pts[c], pts[d]) > dist(pts[a], pts[c])+dist(pts[b], pts[d]):
                    tour[i+1:j+1] = reversed(tour[i+1:j+1])
                    improved = True
    return tour

def three_opt(tour, pts):
    n = len(tour)
    for i in range(n-5):
        for j in range(i+2, n-3):
            for k in range(j+2, n-1):
                a,b,c,d,e,f = tour[i],tour[i+1],tour[j],tour[j+1],tour[k],tour[(k+1)%n]
                old = dist(pts[a], pts[b])+dist(pts[c], pts[d])+dist(pts[e], pts[f])
                new = dist(pts[a], pts[c])+dist(pts[b], pts[e])+dist(pts[d], pts[f])
                if new < old:
                    tour[i+1:j+1] = reversed(tour[i+1:j+1])
                    tour[j+1:k+1] = reversed(tour[j+1:k+1])
    return tour

def lk_light(tour, pts, iters=LK_ITERS):
    best = tour_length(tour, pts)
    t0 = time.perf_counter()
    for _ in range(iters):
        i,j = sorted(random.sample(range(len(tour)),2))
        tour[i:j] = reversed(tour[i:j])
        L = tour_length(tour, pts)
        if L < best: best = L
        else: tour[i:j] = reversed(tour[i:j])
    t1 = time.perf_counter()
    return best, t1-t0

# ================= SINGLE INSTANCE BENCH =================
def run_single(tsp_path, output_txt_path):
    pts,opt = parse_tsp(tsp_path)
    n = len(pts)
    results = []

    for name, algo in [("MHLPQI", mhlpqi)]:
        print(f"Running {name}...")
        t0 = time.perf_counter()
        tour = algo(pts)
        t_init = time.perf_counter() - t0

        L_before2 = tour_length(tour, pts)
        gap_before2 = pct_gap(L_before2, opt)

        tour2 = two_opt(tour[:], pts)
        L_after2 = tour_length(tour2, pts)
        gap_after2 = pct_gap(L_after2, opt)

        if n <= THREE_OPT_LIMIT:
            tour3 = three_opt(tour2[:], pts)
            L_after3 = tour_length(tour3, pts)
            gap_after3 = pct_gap(L_after3, opt)
        else:
            tour3 = tour2
            L_after3 = L_after2
            gap_after3 = gap_after2

        L_lk, t_lk = lk_light(tour3[:], pts)
        gap_lk = pct_gap(L_lk, opt)

        results.append({
            "name": name,
            "before_2opt": (L_before2, gap_before2),
            "after_2opt": (L_after2, gap_after2),
            "after_3opt": (L_after3, gap_after3),
            "after_LK": (L_lk, gap_lk),
            "init_time": t_init,
            "lk_time": t_lk
        })

    # Write to TXT
    with open(output_txt_path, "w") as f:
        f.write(f"TSP file: {tsp_path}\nCities: {n}\nOptimal: {opt}\n\n")
        for r in results:
            f.write(f"--- {r['name']} ---\n")
            f.write(f"Before 2-OPT: {r['before_2opt'][0]:.2f}, Gap%: {r['before_2opt'][1]}\n")
            f.write(f"After 2-OPT:  {r['after_2opt'][0]:.2f}, Gap%: {r['after_2opt'][1]}\n")
            f.write(f"After 3-OPT:  {r['after_3opt'][0]:.2f}, Gap%: {r['after_3opt'][1]}\n")
            f.write(f"After LK:     {r['after_LK'][0]:.2f}, Gap%: {r['after_LK'][1]}\n")
            f.write(f"Times (init, LK): {r['init_time']:.4f}s, {r['lk_time']:.4f}s\n\n")

    print(f"Results written to {output_txt_path}")

# ================= ENTRY =================
if __name__=="__main__":
    tsp_file_path = "C:/Users/INDIAN/Documents/TSP-Layered-Priority-Queue-Insertion/dga9698.tsp"
    output_file_path = "C:/Users/INDIAN/Documents/TSP-Layered-Priority-Queue-Insertion/resulttt.txt"
    run_single(tsp_file_path, output_file_path)

import os
import math
import time
import csv
import re
import itertools

# ================= CONFIG =================

ROOT = os.path.dirname(os.path.abspath(__file__))
DATA_DIR = os.path.join(ROOT, "TSPLIB95", "CONCORODE_solved_instances")
OUT_DIR = os.path.join(ROOT, "results")
os.makedirs(OUT_DIR, exist_ok=True)

ROTATION_ANGLES = [0, 15, 30, 45, 60, 75, 90]

# ================= UTIL =================

def dist(a, b):
    return math.hypot(a[0] - b[0], a[1] - b[1])

def tour_length(tour, pts):
    return sum(
        dist(pts[tour[i]], pts[tour[(i + 1) % len(tour)]])
        for i in range(len(tour))
    )

def pct_gap(length, opt):
    if opt is None or opt == 0:
        return None
    return (length - opt) / opt * 100

# ================= TSP PARSER =================

def parse_tsp(path):
    pts = []
    optimal = None

    with open(path) as f:
        for line in f:
            if "Optimal tour length" in line:
                m = re.search(r"(\d+(\.\d+)?)", line)
                if m:
                    optimal = float(m.group(1))
            if line.strip() == "NODE_COORD_SECTION":
                break

        for line in f:
            if line.strip() == "EOF":
                break
            _, x, y = line.split()
            pts.append((float(x), float(y)))

    return pts, optimal

# ================= GEOMETRY =================

def cross(o, a, b):
    return (a[0]-o[0])*(b[1]-o[1]) - (a[1]-o[1])*(b[0]-o[0])

def convex_hull(points):
    idx = sorted(range(len(points)), key=lambda i: points[i])
    if len(idx) <= 2:
        return idx

    lower, upper = [], []

    for i in idx:
        while len(lower) >= 2 and cross(points[lower[-2]], points[lower[-1]], points[i]) <= 0:
            lower.pop()
        lower.append(i)

    for i in reversed(idx):
        while len(upper) >= 2 and cross(points[upper[-2]], points[upper[-1]], points[i]) <= 0:
            upper.pop()
        upper.append(i)

    return lower[:-1] + upper[:-1]

# ================= INSERTION =================

def cheapest_insertion(tour, idx, pts):
    best_pos, best_cost = 0, float("inf")
    for i in range(len(tour)):
        a, b = tour[i], tour[(i + 1) % len(tour)]
        cost = dist(pts[a], pts[idx]) + dist(pts[idx], pts[b]) - dist(pts[a], pts[b])
        if cost < best_cost:
            best_cost = cost
            best_pos = i + 1
    tour.insert(best_pos, idx)

# ================= LPQI =================

def lpqi(points):
    n = len(points)
    hull = convex_hull(points)
    tour = hull[:]
    remaining = set(range(n)) - set(hull)

    while remaining:
        best_p, best_cost, best_pos = None, float("inf"), None
        for p in remaining:
            for i in range(len(tour)):
                a, b = tour[i], tour[(i + 1) % len(tour)]
                cost = dist(points[a], points[p]) + dist(points[p], points[b]) - dist(points[a], points[b])
                if cost < best_cost:
                    best_cost, best_p, best_pos = cost, p, i + 1
        tour.insert(best_pos, best_p)
        remaining.remove(best_p)

    return tour

# ================= MHLPQI (FIXED) =================

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

# ================= ROTATION (FIXED) =================

def rotate(points, angle):
    rad = math.radians(angle)
    c, s = math.cos(rad), math.sin(rad)
    return [(c*x - s*y, s*x + c*y) for x, y in points]

def hull_rotation_lpqi(points):
    best_len = float("inf")
    best_tour = None

    for angle in ROTATION_ANGLES:
        rp = rotate(points, angle)
        tour = lpqi(rp)
        L = tour_length(tour, points)  # evaluate on ORIGINAL points
        if L < best_len:
            best_len, best_tour = L, tour

    return best_tour

# ================= 2-OPT =================

def two_opt(tour, pts):
    improved = True
    while improved:
        improved = False
        for i in range(len(tour) - 2):
            for j in range(i + 2, len(tour)):
                a, b = tour[i], tour[i+1]
                c, d = tour[j], tour[(j+1) % len(tour)]
                if dist(pts[a], pts[b]) + dist(pts[c], pts[d]) > \
                   dist(pts[a], pts[c]) + dist(pts[b], pts[d]):
                    tour[i+1:j+1] = reversed(tour[i+1:j+1])
                    improved = True
    return tour

# ================= SAFE 3-OPT =================

def three_opt(tour, pts):
    n = len(tour)
    for i in range(n - 5):
        for j in range(i + 2, n - 3):
            for k in range(j + 2, n - 1):
                a, b = tour[i], tour[i+1]
                c, d = tour[j], tour[j+1]
                e, f = tour[k], tour[(k+1) % n]

                old = dist(pts[a], pts[b]) + dist(pts[c], pts[d]) + dist(pts[e], pts[f])
                new = dist(pts[a], pts[c]) + dist(pts[b], pts[e]) + dist(pts[d], pts[f])

                if new < old:
                    tour[i+1:j+1] = reversed(tour[i+1:j+1])
                    tour[j+1:k+1] = reversed(tour[j+1:k+1])
    return tour

# ================= BENCH =================

def run():
    rows = []

    for file in sorted(os.listdir(DATA_DIR)):
        if not file.endswith(".tsp"):
            continue

        pts, opt = parse_tsp(os.path.join(DATA_DIR, file))

        for name, algo in [
            ("LPQI", lpqi),
            ("MHLPQI", mhlpqi),
            ("HullRot-LPQI", hull_rotation_lpqi)
        ]:
            t0 = time.perf_counter()
            tour = algo(pts)
            t1 = time.perf_counter()

            L0 = tour_length(tour, pts)

            t2 = time.perf_counter()
            tour2 = two_opt(tour[:], pts)
            t3 = time.perf_counter()

            L2 = tour_length(tour2, pts)

            t4 = time.perf_counter()
            tour3 = three_opt(tour2[:], pts)
            t5 = time.perf_counter()

            L3 = tour_length(tour3, pts)

            rows.append([
                file, len(pts), name,
                L0, pct_gap(L0, opt),
                L2, pct_gap(L2, opt),
                L3, pct_gap(L3, opt),
                t1-t0, t3-t2, t5-t4
            ])
            print(rows)

    out = os.path.join(OUT_DIR, "concorde_full_bench.csv")
    with open(out, "w", newline="") as f:
        writer = csv.writer(f)
        writer.writerow([
            "instance", "n", "algorithm",
            "initial_len", "initial_gap_pct",
            "2opt_len", "2opt_gap_pct",
            "3opt_len", "3opt_gap_pct",
            "init_time", "2opt_time", "3opt_time"
        ])
        writer.writerows(rows)

    print("DONE →", out)

# ================= ENTRY =================
if __name__ == "__main__":
    run()

/* Exhaustive count of extreme half-one metrics on n points.
   d extreme  <=>  no component of Gamma_d is bipartite. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int n, m;
static int eidx[16][16];
static int tri_u[4000], tri_v[4000], tri_w[4000];
static int ntri;

static void build(void) {
    int t = 0;
    for (int i = 0; i < n; i++)
        for (int j = i + 1; j < n; j++) { eidx[i][j] = eidx[j][i] = t++; }
    m = t;
    ntri = 0;
    for (int i = 0; i < n; i++)
        for (int j = i + 1; j < n; j++)
            for (int k = j + 1; k < n; k++) {
                int ap[3][3] = {{i,j,k},{j,i,k},{k,i,j}};
                for (int s = 0; s < 3; s++) {
                    int a = ap[s][0], b = ap[s][1], c = ap[s][2];
                    tri_u[ntri] = eidx[a][b];
                    tri_v[ntri] = eidx[a][c];
                    tri_w[ntri] = eidx[b][c];
                    ntri++;
                }
            }
}

static unsigned int adj[32];
static int colour[32];
static int stackv[32];

static int is_extreme(unsigned int mask) {
    for (int t = 0; t < m; t++) adj[t] = 0;
    for (int t = 0; t < ntri; t++) {
        int u = tri_u[t], v = tri_v[t], w = tri_w[t];
        if (((mask >> u) & 1u) && ((mask >> v) & 1u) && !((mask >> w) & 1u)) {
            adj[u] |= 1u << v;
            adj[v] |= 1u << u;
        }
    }
    unsigned int rem = mask;
    while (rem) {
        int s = __builtin_ctz(rem);
        unsigned int comp = 1u << s;
        int sp = 0, bip = 1;
        colour[s] = 0;
        stackv[sp++] = s;
        while (sp) {
            int u = stackv[--sp];
            unsigned int a = adj[u];
            while (a) {
                int v = __builtin_ctz(a);
                a &= a - 1;
                if (!((comp >> v) & 1u)) {
                    colour[v] = 1 - colour[u];
                    comp |= 1u << v;
                    stackv[sp++] = v;
                } else if (colour[v] == colour[u]) bip = 0;
            }
        }
        if (bip) return 0;
        rem &= ~comp;
    }
    return 1;
}

int main(int argc, char **argv) {
    int lo = atoi(argv[1]), hi = atoi(argv[2]);
    for (n = lo; n <= hi; n++) {
        build();
        unsigned long long cnt = 0, tot = 1ULL << m;
        for (unsigned long long mask = 0; mask < tot; mask++)
            if (is_extreme((unsigned int)mask)) cnt++;
        printf("n=%d  2^m=%llu  |ex(H_n)|=%llu  ratio=%.6f\n",
               n, tot, cnt, (double)cnt / (double)tot);
        fflush(stdout);
    }
    return 0;
}

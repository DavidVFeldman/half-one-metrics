/* Count extreme points (vertices) of the metric body Mbar_n by exhaustive search
   over all points with denominator dividing L.  Rank of the tight-constraint
   system computed mod a large prime.  Verifies the dissertation's Tables 4.1.1-2. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MOD 1000003LL
static int n, m, L;
static int eidx[10][10];
static int tri[400][3];      /* (long, short1, short2) index triples */
static int ntri;

static void build(void) {
    int t = 0;
    for (int i = 0; i < n; i++)
        for (int j = i + 1; j < n; j++) { eidx[i][j] = eidx[j][i] = t++; }
    m = t; ntri = 0;
    for (int i = 0; i < n; i++)
        for (int j = i + 1; j < n; j++)
            for (int k = j + 1; k < n; k++) {
                int ij = eidx[i][j], ik = eidx[i][k], jk = eidx[j][k];
                tri[ntri][0]=ik; tri[ntri][1]=ij; tri[ntri][2]=jk; ntri++;
                tri[ntri][0]=ij; tri[ntri][1]=ik; tri[ntri][2]=jk; ntri++;
                tri[ntri][0]=jk; tri[ntri][1]=ij; tri[ntri][2]=ik; ntri++;
            }
}

static long long rows[200][16];
static int nrows;

static long long inv(long long a) {
    long long r = 1, e = MOD - 2;
    a %= MOD;
    while (e) { if (e & 1) r = r * a % MOD; a = a * a % MOD; e >>= 1; }
    return r;
}

static int rank_mod(void) {
    int rk = 0;
    for (int c = 0; c < m && rk < nrows; c++) {
        int p = -1;
        for (int i = rk; i < nrows; i++) if (rows[i][c] % MOD) { p = i; break; }
        if (p < 0) continue;
        for (int j = 0; j < m; j++) { long long tmp = rows[rk][j]; rows[rk][j] = rows[p][j]; rows[p][j] = tmp; }
        long long iv = inv(rows[rk][c]);
        for (int j = 0; j < m; j++) rows[rk][j] = rows[rk][j] % MOD * iv % MOD;
        for (int i = 0; i < nrows; i++) {
            if (i != rk && rows[i][c] % MOD) {
                long long f = rows[i][c] % MOD;
                for (int j = 0; j < m; j++)
                    rows[i][j] = ((rows[i][j] - f * rows[rk][j]) % MOD + MOD) % MOD;
            }
        }
        rk++;
    }
    return rk;
}

int main(int argc, char **argv) {
    n = atoi(argv[1]); L = atoi(argv[2]);
    build();
    int d[16];
    long long total = 1;
    for (int i = 0; i < m; i++) total *= (L + 1);
    long long metrics = 0, verts = 0, pd = 0;
    for (long long code = 0; code < total; code++) {
        long long c = code;
        for (int i = 0; i < m; i++) { d[i] = c % (L + 1); c /= (L + 1); }
        int ok = 1;
        for (int t = 0; t < ntri && ok; t++)
            if (d[tri[t][0]] > d[tri[t][1]] + d[tri[t][2]]) ok = 0;
        if (!ok) continue;
        metrics++;
        nrows = 0;
        for (int i = 0; i < m; i++)
            if (d[i] == 0 || d[i] == L) {
                memset(rows[nrows], 0, sizeof(long long) * 16);
                rows[nrows][i] = 1; nrows++;
            }
        for (int t = 0; t < ntri; t++)
            if (d[tri[t][0]] == d[tri[t][1]] + d[tri[t][2]]) {
                memset(rows[nrows], 0, sizeof(long long) * 16);
                rows[nrows][tri[t][0]] += 1;
                rows[nrows][tri[t][1]] = (rows[nrows][tri[t][1]] + MOD - 1) % MOD;
                rows[nrows][tri[t][2]] = (rows[nrows][tri[t][2]] + MOD - 1) % MOD;
                nrows++;
            }
        if (nrows < m) continue;
        if (rank_mod() == m) {
            verts++;
            int pos = 1;
            for (int i = 0; i < m; i++) if (d[i] == 0) pos = 0;
            if (pos) pd++;
        }
    }
    printf("n=%d L=%d : %lld grid points, %lld metrics, %lld vertices "
           "(%lld positive-definite)\n", n, L, total, metrics, verts, pd);
    return 0;
}

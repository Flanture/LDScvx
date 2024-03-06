//
// Created by MA Chenhao on 29/11/2021.
//
#include "Graph.h"
#include <ctime>
#include <iostream>

#define DELTA 1e-5

Graph::Graph(FILE *file, int NT, int topk) {
    printf("Graph construction\n");
    fscanf(file, "%d%lu", &n, &m);

    adj.resize(n);
    r.resize(n);
    deg.resize(n);
    core.resize(n);
    selected.resize(n, true);
    active.resize(n, true);
    lds_num.resize(n, -1);
    num_verify = 0;
    veri_vtx.resize(n, 0);
    rho_gu.resize(n);
    rho_u.resize(n);
    rho_l.resize(n);
    val.resize(n);
    nag.resize(n);
    sg.resize(n);
    fa.resize(n);
    slt_nodes.clear();
    slt_edges.clear();
    slt_h_cliques.clear();

//    printf("ok1\n");
    for (int i = 0; i < m; i++) {
        int u, v;
        fscanf(file, "%d%d", &u, &v);
        edges.emplace_back(u, v);
        adj[u].push_back(v);
        adj[v].push_back(u);
    }
    alpha.resize(m);
    alpha_c.resize(hc_num);
//    printf("ok2\n");

    this->NT = NT;
    this->topk = topk;
}

EdgeList* ReadEdgeList(char* file_name) {
    unsigned e1 = MAX_EDGES;
    EdgeList* el = (EdgeList*)malloc(sizeof(EdgeList));
    FILE* file = fopen(file_name, "r");
    el->n = 0;
    el->e = 0;
    el->edges = (Edge*)malloc(e1 * sizeof(Edge));
    while (fscanf(file, "%u %u", &(el->edges[el->e].s), &(el->edges[el->e].t)) == 2) { // Read one edge
        el->n = max3(el->n, el->edges[el->e].s, el->edges[el->e].t);
        ++el->e;
        if (el->e == e1) {
            e1 += MAX_EDGES;
            el->edges = (Edge*)realloc(el->edges, e1 * sizeof(Edge));
        }
    }
    fclose(file);
    ++el->n; // So the nodes are numbered from 0 to el->n - 1
    el->edges = (Edge*)realloc(el->edges, el->e * sizeof(Edge));
    return el;
}


void Graph::enumerateKCliques(int k) {
    h_cliques.clear();
    vector<int> currentClique; // 当前候选 k-clique 的节点集合
    backtrack(0, k, currentClique);
}

void Graph::backtrack(int currentNode, int k, vector<int>& currentClique) {
    if (currentClique.size() == k) {
        h_cliques.push_back(currentClique);
        
        // 当前候选 k-clique 已满足大小要求，处理它（如输出或其他操作）
        // 在这里你可以自定义处理方式，比如输出当前 k-clique 的节点
        for (int node : currentClique) {
            cout << node << " ";
            v2cliques[node].push_back(h_cliques.size() - 1);
        }
        cout << endl;
        return;
    }

    for (int i = currentNode; i < n; ++i) {
        if (isValidAddition(currentClique, i)) {
            currentClique.push_back(i);
            backtrack(i + 1, k, currentClique);
            currentClique.pop_back();
        }
    }
}

bool Graph::isValidAddition(const vector<int>& currentClique, int newNode) {
    for (int node : currentClique) {
        bool found = false;
        for (int neighbor : adj[node]) {
            if (neighbor == newNode) {
                found = true;
                break;
            }
        }
        if (!found) {
            return false;
        }
    }
    return true;
}


//void Graph::clique_enum()
//{
//    for (int i = 0; i < edges.size(); ++i) {
//
//    }
//}

void Graph::frank_wolfe() {
    printf("#node %lld #edge %lld\n", slt_nodes.size(), slt_edges.size());
    if (CT == 0) {
        for (auto &edge: slt_edges) {
            alpha[edge] = 0.5;
        }
    }

    for (auto & node : slt_nodes) {
        r[node] = 0;
    }
    for (auto & e : slt_edges) {
        r[edges[e].first] += alpha[e];
        r[edges[e].second] += 1 - alpha[e];
    }


    for (int t = CT + 1; t <= CT + NT; t++) {
        double gamma_t = 2.0 / (t + 2);
        for (auto & e : slt_edges) {
//            alpha[e] *= 1 - gamma_t;
            if (r[edges[e].first] < r[edges[e].second]) {
                r[edges[e].first] += gamma_t * (1 - alpha[e]);
                r[edges[e].second] -= gamma_t * (1 - alpha[e]);
                alpha[e] = alpha[e] * (1 - gamma_t) + gamma_t;
            }
            else if (r[edges[e].first] > r[edges[e].second]) {
                r[edges[e].first] -= gamma_t * alpha[e];
                r[edges[e].second] += gamma_t * alpha[e];
                alpha[e] = alpha[e] * (1 - gamma_t);
            }
        }
//        for (auto & node : slt_nodes) {
//            r[node] = 0;
//        }
//        for (auto & e : slt_edges) {
//            r[edges[e].first] += alpha[e];
//            r[edges[e].second] += 1 - alpha[e];
//        }
    }
//    for (int i = 0; i < n; i++) {
//        printf("%.4f ", r[i]);
//    }
//    printf("\n");
}

void Graph::frank_wolfe_h_clique() {
    if (CT == 0) {
        alpha_c.resize(h_cliques.size());
        for (auto& hc : slt_h_cliques) {
            for (auto& hc_node : h_cliques[hc]) {
                alpha_c[hc][hc_node] = 1 / float(h);
                r[hc_node] += alpha_c[hc][hc_node];
            }
        }

    }

    //for (int t = CT + 1; t <= CT + NT; t++) {
    for (int t = CT / 2 + 1; t <= CT; ++t) {
        double gamma_t = 1 / double(t + 1);
        for (auto& hc : slt_h_cliques) {
            for (auto& hc_node : h_cliques[hc]) {
                alpha_c[hc][hc_node] *= 1 - gamma_t;
            }
        }
        for (auto& node : slt_nodes) {
            r[node] *= 1 - gamma_t;
        }
        for (auto& hc : slt_h_cliques) {
            int node_index = h_cliques[hc][0];
            for (auto& hc_node : h_cliques[hc]) {
                if (r[hc_node] < r[node_index]) {
                    node_index = hc_node;
                }
            }
            r[node_index] += gamma_t;
            alpha_c[hc][node_index] += gamma_t;
        }


    }

    for (auto& node : slt_nodes) {
        printf("rho[%d]: %f\n", node, r[node]);
    }


}

/* Pool Adjacent Violators Algorithm. Try to decompose the graph into Stable Groups.
 * deg reused here!
 */
void Graph::pava() {
    // 对 slt_nodes 按照 r 值进行降序排序
    sort(slt_nodes.begin(), slt_nodes.end(), [this](int a, int b)->bool {
        return r[a] > r[b];
        });

    // 更新 deg 数组，deg 存储节点在 slt_nodes 中的位置
    for (int i = 0; i < slt_nodes.size(); i++) {
        deg[slt_nodes[i]] = i;
    }

    // 计算节点之间的连接数  ne[i]表示slt_nodes[i]顶点的边数
    vector<int> ne(slt_nodes.size(), 0);
    for (auto e : slt_edges) {
        int u = deg[edges[e].first];
        int v = deg[edges[e].second];
        ne[(u > v) ? u : v]++;
    }

    // 初始化 nsg、nag、val 数组
    nag[0] = 1;
    val[0] = ne[0];
    nsg = 0;

    // 执行 PAVA 算法
    // nag 用于表示每个稳定群中节点的数量
    // nsg 用于表示当前的稳定群数量
    for (int i = 1; i < slt_nodes.size(); i++) {
        nsg += 1;            // 增加稳定群数量
        val[nsg] = ne[i];    // 将节点之间的连接数存储到 val 数组中
        nag[nsg] = 1;        // 初始化 nag 数组

        while ((nsg > 0) && (val[nsg] > val[nsg - 1] - 1e-5)) {
            // 进入循环，执行合并稳定群的过程
            val[nsg - 1] = (nag[nsg] * val[nsg] + nag[nsg - 1] * val[nsg - 1]) / (nag[nsg] + nag[nsg - 1]);
            nag[nsg - 1] += nag[nsg];  // 更新 nag 数组
            nsg--;                    // 减少稳定群数量
        }
    }
    nsg++;  // 增加稳定群数量（nsg 最初是 0，所以要加 1）


    printf("nsg %d\n", nsg);

    // 更新 sg 数组: 记录每一个节点属于哪个稳定群
    int cur = 0;
    for (int i = 0; i < nsg; i++) {
        for (int j = cur; j < cur + nag[i]; j++) {
            sg[slt_nodes[j]] = i;
        }
        cur += nag[i];
    }

}

int max(vector<int> h_clique) {
    int max_node = 0;
    for (auto& hc_node : h_clique) {
        if (hc_node > max_node) max_node = hc_node;
    }
    return max_node;
}


int max(vector<int> sg, vector<int> h_clique) {
    int max_sg = 0;
    for (auto& hc_node : h_clique) {
        if (sg[hc_node] > max_sg) max_sg = sg[hc_node];
    }
    return max_sg;
}

int min(vector<int> h_clique) {
    int min_node = INT_MAX;
    for (auto& hc_node : h_clique) {
        if (hc_node < min_node) min_node = hc_node;
    }
    return min_node;
}


int min(vector<int> sg, vector<int> h_clique) {
    int min_sg = INT_MAX;
    for (auto& hc_node : h_clique) {
        if (sg[hc_node] < min_sg) min_sg = sg[hc_node];
    }
    return min_sg;
}

void Graph::pava_h_clique() {
    // 对 slt_nodes 按照 r 值进行降序排序
    sort(slt_nodes.begin(), slt_nodes.end(), [this](int a, int b)->bool {
        return r[a] > r[b];
        });

    // 更新 deg 数组，deg 存储节点在 slt_nodes 中的位置
    std::fill(deg.begin(), deg.end(), -1);
    for (int i = 0; i < slt_nodes.size(); i++) {
        deg[slt_nodes[i]] = i;
    }

    // 计算节点之间的连接数  nc[i]表示slt_nodes[i]顶点的h-cliques数
    vector<int> nc(slt_nodes.size(), 0);
    for (auto& hc : slt_h_cliques) {
        int max_node = max(deg, h_cliques[hc]);
        nc[max_node]++;
    }

    // 初始化 nsg、nag、val 数组
    nag[0] = 1;
    val[0] = nc[0];
    nsg = 0;

    // 执行 PAVA 算法
    // nag 用于表示每个稳定群中节点的数量
    // nsg 用于表示当前的稳定群数量
    for (int i = 1; i < slt_nodes.size(); i++) {
        nsg += 1;            // 增加稳定群数量
        val[nsg] = nc[i];    // 将节点之间的h-cliques数存储到 val 数组中
        nag[nsg] = 1;        // 初始化 nag 数组

        while ((nsg > 0) && (val[nsg] > val[nsg - 1] - 1e-5)) {
            // 进入循环，执行合并稳定群的过程
            val[nsg - 1] = (nag[nsg] * val[nsg] + nag[nsg - 1] * val[nsg - 1]) / (nag[nsg] + nag[nsg - 1]);
            nag[nsg - 1] += nag[nsg];  // 更新 nag 数组
            nsg--;                    // 减少稳定群数量
        }
    }
    nsg++;  // 增加稳定群数量（nsg 最初是 0，所以要加 1）


    printf("nsg %d\n", nsg);

    // 更新 sg 数组: 记录每一个节点属于哪个稳定群
    int cur = 0;
    for (int i = 0; i < nsg; i++) {
        for (int j = cur; j < cur + nag[i]; j++) {
            sg[slt_nodes[j]] = i;
        }
        cur += nag[i];
    }
}

//void Graph::check_sg_h_cliques() {
//    for (int i = 0; i < h_cliques.size(); ++i) { //遍历h-cliques
//        int max_sg = -1;
//        // 找到h-clique中顶点所属stable group的最大编号
//        for (auto& hc_node : h_cliques[i]) {
//            if (sg[hc_node] > max_sg) max_sg = sg[hc_node];
//        }
//        double s = 0;
//        int num = 0;
//        for (auto& hc_node : h_cliques[i]) {
//            if (sg[hc_node] != max_sg) {
//                s += alpha_c[i][hc_node];
//                alpha_c[i][hc_node] = 0;
//                num++;
//            }
//        }
//        for (auto& hc_node : h_cliques[i]) {
//            if (sg[hc_node] == max_sg) {
//                alpha_c[i][hc_node] += s / num;
//            }
//        }
//
//    }
//}

void Graph::check_sg_h_clique() {
    // 如果只有一个或没有稳定群，无需处理，直接返回
    if (nsg <= 1) return;

    // TODO 对 slt_edges 中的边按照一定规则排序，确保后续处理的顺序
    sort(slt_h_cliques.begin(), slt_h_cliques.end(), [this](int a, int b)->bool {
        int a1 = min(sg, h_cliques[a]);
        int a2 = max(sg, h_cliques[a]);
        int b1 = min(sg, h_cliques[b]);
        int b2 = max(sg, h_cliques[b]);
        if (a1 != b1)
            return a1 < b1;
        else
            return a2 < b2;
        });

    // 创建用于存储每个稳定群是否有效的数组
    vector<bool> valid(nsg);

    // 创建用于计算每个稳定群中h-cliques的数量的数组
    vector<int> bin(nsg + 1, 0);

    // 计算每个稳定群中的h-cliques数，并将结果存储在 bin 数组中
    for (auto& hc : slt_h_cliques) {
        // 首先计算当前h_cliques所连接的节点的稳定群中较小的一个，
        // 并将结果存储在变量 a 中。
        // 这是为了确保h-clique被计数到稳定群的最小节点中    
        int a = min(sg, h_cliques[hc]);
        ++bin[a];
    }


    // 代码计算了一个累积的数组 bin，
    // 使得对每个稳定群的累积h-cliques数可以以常量时间复杂度访问
    int s = 0;
    for (int i = 0; i <= nsg; i++) {
        int tmp = s;
        s += bin[i];
        bin[i] = tmp;
    }

    // 创建用于存储每个稳定群中节点的最大 r 值的数组
    vector<double> max_r(nsg);

    int cur = 0;
    for (int i = 0; i < nsg; i++) {
        // 初始化每个稳定群的最大 r 值
        max_r[i] = r[slt_nodes[cur]];

        // 计算每个稳定群中节点的最大 r 值
        for (int j = cur + 1; j < cur + nag[i]; j++) {
            max_r[i] = max(max_r[i], r[slt_nodes[j]]);
        }
        cur += nag[i];
    }

    // 初始化整个图中节点的最小 r 值
    double min_r = r[slt_nodes[0]]; // 初始化最小 r 值为第一个稳定群中节点的 r 值
    cur = 0; // 初始化稳定群中节点索引为0
    vector<int> cpt(bin); // 创建 bin 数组的副本，用于回滚操作
    clock_t start = clock(); // 记录处理开始的时间

    for (int i = 0; i < nsg - 1; i++) { // 迭代处理从第一个稳定群到倒数第二个稳定群的情况
        for (int j = cur; j < cur + nag[i]; j++) { // 计算当前稳定群 i 中节点的最小 r 值
            min_r = min(min_r, r[slt_nodes[j]]);
        }
        double min_t = min_r; // 初始化当前最小 r 值为 min_r

        vector<double> max_tmp(max_r.begin() + i + 1, max_r.end()); // 创建最大 r 值数组 max_tmp
        double max_t = *max_element(begin(max_tmp), end(max_tmp)); // 计算最大 r 值 max_t

        queue<tuple<int, int, unordered_map<int, double>>> q; // 创建队列 q 用于回滚操作
        valid[i] = true; // 假设当前稳定群有效

        for (int j = 0; j <= i; j++) { // 迭代处理从第一个稳定群到当前稳定群 i 的情况

            while (cpt[j] < bin[j + 1]) { // 遍历当前稳定群范围内未处理的h-clique  ！！假设这里顺序可以对应上
                int hc = slt_h_cliques[cpt[j]]; // 获取当前未处理的h-clique
                int max_sg = max(sg, h_cliques[hc]);

                if (max_sg > i) { // 检查h-clique是否跨越当前稳定群
                    q.push(make_tuple(j, cpt[j], alpha_c[hc])); // 存储需要回滚的h-clique和相关信息

                    double s = 0;
                    int num = 0;
                    for (auto& hc_node : h_cliques[hc]) {
                        if (sg[hc_node] != max_sg) {
                            s += alpha_c[hc][hc_node];
                            r[hc_node] -= alpha_c[hc][hc_node];
                            min_t = min(min_t, r[hc_node]);
                            alpha_c[hc][hc_node] = 0;
                            num++;
                        }
                    }
                    for (auto& hc_node : h_cliques[hc]) {
                        if (sg[hc_node] == max_sg) {
                            r[hc_node] += s / num;
                            max_r[sg[hc_node]] = max(max_r[sg[hc_node]], r[hc_node]);
                            max_t = max(max_t, r[hc_node]);
                            alpha_c[hc][hc_node] += s / num;
                        }          
                    }
                    if (min_t <= max_t) {
                        valid[i] = false; // 如果条件不满足，标记当前稳定群为无效
                        break;
                    }
                }

                ++cpt[j]; // 增加当前稳定群中边的计数器
            }

            if (!valid[i]) break; // 如果当前稳定群无效，终止内部循环
        }

        if (valid[i]) {
            min_r = min(min_t, min_r); // 如果当前稳定群有效，更新最小 r 值
        }
        else {
            // 如果当前稳定群无效，回滚 max_r 数组的值和节点 r 值和 alpha 值
            for (int j = i + 1; j < max_r.size(); j++) {
                max_r[j] = max_tmp[j - i - 1];
            }

            while (!q.empty()) {
                auto tp = q.front();
                q.pop();
                cpt[get<0>(tp)] = min(cpt[get<0>(tp)], get<1>(tp)); //这一行的目的是什么

                int hc = slt_h_cliques[get<1>(tp)];
                int max_sg = max(sg, h_cliques[hc]);

                double s = 0;
                int num = 0;
                for (auto& hc_node : h_cliques[hc]) {
                    if (sg[hc_node] != max_sg) {
                        s += get<2>(tp)[hc_node];
                        r[hc_node] += get<2>(tp)[hc_node];
                        alpha_c[hc][hc_node] = get<2>(tp)[hc_node];
                        num++;
                    }
                }
                for (auto& hc_node : h_cliques[hc]) {
                    if (sg[hc_node] == max_sg) {
                        r[hc_node] -= s / num;
                        alpha_c[hc][hc_node] -= s / num;
                    }
                }
            }
        }

        clock_t cur_t = clock(); // 记录当前处理完成的时间
    }


    // 更新 check_first 变量以表示是否为第一个稳定群或第一个稳定群是否有效
    check_first = (nsg == 1) || valid[0];

    // 如果存在多个稳定群，合并它们
    if (nsg > 1) {
        vector<int> n_nag;
        for (int i = 0; i < nsg; i++) {
            // 检查是否当前稳定群是第一个稳定群（索引为0），或者前一个稳定群有效
            if (i == 0 || valid[i - 1]) {
                // 如果是第一个稳定群或前一个稳定群有效，则创建一个新的稳定群
                // 并将当前稳定群的节点数量添加到新的稳定群中
                n_nag.push_back(nag[i]);
            }
            else {
                // 如果不是第一个稳定群且前一个稳定群无效，则将当前稳定群与前一个稳定群合并
                // 将当前稳定群的节点数量添加到前一个稳定群的节点数量中
                n_nag[n_nag.size() - 1] += nag[i];
            }

        }
        nag = n_nag; // 更新 nag 数组以反映合并后的稳定群

        cur = 0; // 初始化稳定群节点索引为0
        nsg = nag.size(); // 更新稳定群的数量
        double minr = m; // 初始化最小 r 值为 m（一个较大的值，作为初始值）

        // 迭代处理每个稳定群
        for (int i = 0; i < nsg; i++) {
            double tmp_r = m; // 初始化当前稳定群的最小 r 值为 m

            // 更新当前稳定群中节点的 sg（稳定群索引），并计算最小 r 值
            for (int j = cur; j < cur + nag[i]; j++) {
                sg[slt_nodes[j]] = i; // 更新节点的稳定群索引
                tmp_r = min(tmp_r, r[slt_nodes[j]]); // 计算当前稳定群的最小 r 值
                minr = min(minr, r[slt_nodes[j]]); // 更新整体最小 r 值
            }
            cur += nag[i]; // 更新节点索引，准备处理下一个稳定群
        }
    }


    // 输出更新后的稳定群数量
    printf("updated nsg %d\n", nsg);
}

void Graph::check_sg() {
    // 如果只有一个或没有稳定群，无需处理，直接返回
    if (nsg <= 1) return;

    // 对 slt_edges 中的边按照一定规则排序，确保后续处理的顺序
    sort(slt_edges.begin(), slt_edges.end(), [this](int a, int b)->bool {
        int a1 = min(sg[edges[a].first], sg[edges[a].second]);
        int a2 = max(sg[edges[a].first], sg[edges[a].second]);
        int b1 = min(sg[edges[b].first], sg[edges[b].second]);
        int b2 = max(sg[edges[b].first], sg[edges[b].second]);
        if (a1 != b1)
            return a1 < b1;
        else
            return a2 < b2;
        });

    // 创建用于存储每个稳定群是否有效的数组
    vector<bool> valid(nsg);

    // 创建用于计算每个稳定群中边的数量的数组
    vector<int> bin(nsg + 1, 0);

    // 计算每个稳定群中的边数，并将结果存储在 bin 数组中
    for (int i = 0; i < slt_edges.size(); i++) {
       // 首先计算当前边 slt_edges[i] 所连接的两个节点的稳定群中较小的一个，
       // 并将结果存储在变量 a 中。
       // 这是为了确保边被计数到稳定群的最小节点中
        int a = min(sg[edges[slt_edges[i]].first], sg[edges[slt_edges[i]].second]);  
        ++bin[a];
    }


    // 代码计算了一个累积的数组 bin，
    // 使得对每个稳定群的累积边数可以以常量时间复杂度访问
    int s = 0;
    for (int i = 0; i <= nsg; i++) {
        int tmp = s;
        s += bin[i];
        bin[i] = tmp;
    }

    // 创建用于存储每个稳定群中节点的最大 r 值的数组
    vector<double> max_r(nsg);

    int cur = 0;
    for (int i = 0; i < nsg; i++) {
        // 初始化每个稳定群的最大 r 值
        max_r[i] = r[slt_nodes[cur]];

        // 计算每个稳定群中节点的最大 r 值
        for (int j = cur + 1; j < cur + nag[i]; j++) {
            max_r[i] = max(max_r[i], r[slt_nodes[j]]);
        }
        cur += nag[i];
    }

    // 初始化整个图中节点的最小 r 值
    double min_r = r[slt_nodes[0]]; // 初始化最小 r 值为第一个稳定群中节点的 r 值
    cur = 0; // 初始化稳定群中节点索引为0
    vector<int> cpt(bin); // 创建 bin 数组的副本，用于回滚操作
    clock_t start = clock(); // 记录处理开始的时间

    for (int i = 0; i < nsg - 1; i++) { // 迭代处理从第一个稳定群到倒数第二个稳定群的情况
        for (int j = cur; j < cur + nag[i]; j++) { // 计算当前稳定群 i 中节点的最小 r 值
            min_r = min(min_r, r[slt_nodes[j]]);
        }
        double min_t = min_r; // 初始化当前最小 r 值为 min_r

        vector<double> max_tmp(max_r.begin() + i + 1, max_r.end()); // 创建最大 r 值数组 max_tmp
        double max_t = *max_element(begin(max_tmp), end(max_tmp)); // 计算最大 r 值 max_t

        queue<tuple<int, int, double>> q; // 创建队列 q 用于回滚操作
        valid[i] = true; // 假设当前稳定群有效

        for (int j = 0; j <= i; j++) { // 迭代处理从第一个稳定群到当前稳定群 i 的情况
            while (cpt[j] < bin[j + 1]) { // 遍历当前稳定群范围内未处理的边
                int e = slt_edges[cpt[j]]; // 获取当前未处理的边 e

                if (max(sg[edges[e].first], sg[edges[e].second]) > i) { // 检查边是否跨越当前稳定群
                    q.push(make_tuple(j, cpt[j], alpha[e])); // 存储需要回滚的边和相关信息

                    int u = edges[e].first;
                    int v = edges[e].second;

                    if (sg[u] > sg[v]) {
                        r[u] += 1 - alpha[e];
                        r[v] -= 1 - alpha[e];
                        max_r[sg[u]] = max(max_r[sg[u]], r[u]);
                        max_t = max(max_t, r[u]);
                        min_t = min(min_t, r[v]);
                        alpha[e] = 1;
                    }
                    else {
                        r[u] -= alpha[e];
                        r[v] += alpha[e];
                        min_t = min(min_t, r[u]);
                        max_r[sg[v]] = max(max_r[sg[v]], r[v]);
                        max_t = max(max_t, r[v]);
                        alpha[e] = 0;
                    }

                    if (min_t <= max_t) {
                        valid[i] = false; // 如果条件不满足，标记当前稳定群为无效
                        break;
                    }
                }

                ++cpt[j]; // 增加当前稳定群中边的计数器
            }

            if (!valid[i]) break; // 如果当前稳定群无效，终止内部循环
        }

        if (valid[i]) {
            min_r = min(min_t, min_r); // 如果当前稳定群有效，更新最小 r 值
        }
        else {
            // 如果当前稳定群无效，回滚 max_r 数组的值和节点 r 值和 alpha 值
            for (int j = i + 1; j < max_r.size(); j++) {
                max_r[j] = max_tmp[j - i - 1];
            }

            while (!q.empty()) {
                auto tp = q.front();
                q.pop();
                cpt[get<0>(tp)] = min(cpt[get<0>(tp)], get<1>(tp));
                int e = slt_edges[get<1>(tp)];
                int u = edges[e].first, v = edges[e].second;
                r[u] += get<2>(tp) - alpha[e];
                r[v] -= get<2>(tp) - alpha[e];
                alpha[e] = get<2>(tp);
            }
        }

        clock_t cur_t = clock(); // 记录当前处理完成的时间
    }


    // 更新 check_first 变量以表示是否为第一个稳定群或第一个稳定群是否有效
    check_first = (nsg == 1) || valid[0];

    // 如果存在多个稳定群，合并它们
    if (nsg > 1) {
        vector<int> n_nag;
        for (int i = 0; i < nsg; i++) {
            // 检查是否当前稳定群是第一个稳定群（索引为0），或者前一个稳定群有效
            if (i == 0 || valid[i - 1]) {
                // 如果是第一个稳定群或前一个稳定群有效，则创建一个新的稳定群
                // 并将当前稳定群的节点数量添加到新的稳定群中
                n_nag.push_back(nag[i]);
            }
            else {
                // 如果不是第一个稳定群且前一个稳定群无效，则将当前稳定群与前一个稳定群合并
                // 将当前稳定群的节点数量添加到前一个稳定群的节点数量中
                n_nag[n_nag.size() - 1] += nag[i];
            }

        }
        nag = n_nag; // 更新 nag 数组以反映合并后的稳定群

        cur = 0; // 初始化稳定群节点索引为0
        nsg = nag.size(); // 更新稳定群的数量
        double minr = m; // 初始化最小 r 值为 m（一个较大的值，作为初始值）

        // 迭代处理每个稳定群
        for (int i = 0; i < nsg; i++) {
            double tmp_r = m; // 初始化当前稳定群的最小 r 值为 m

            // 更新当前稳定群中节点的 sg（稳定群索引），并计算最小 r 值
            for (int j = cur; j < cur + nag[i]; j++) {
                sg[slt_nodes[j]] = i; // 更新节点的稳定群索引
                tmp_r = min(tmp_r, r[slt_nodes[j]]); // 计算当前稳定群的最小 r 值
                minr = min(minr, r[slt_nodes[j]]); // 更新整体最小 r 值
            }
            cur += nag[i]; // 更新节点索引，准备处理下一个稳定群
        }
    }


    // 输出更新后的稳定群数量
    printf("updated nsg %d\n", nsg);
}


//void Graph::check_sg() {
//    vector<bool> valid(nsg);
//    queue<pair<int, double>> q;
//    int cur = 0;
//    for (int i = 0; i < nsg - 1; i++){
//        cur += nag[i];
//        for (auto e : slt_edges) {
//            int u = edges[e].first, v = edges[e].second;
//            if (min(sg[u], sg[v]) <= i && max(sg[u], sg[v]) > i) {
//                q.push(make_pair(e, alpha[e]));
//                if (sg[u] > sg[v]) {
//                    r[u] += 1 - alpha[e];
//                    r[v] -= 1 - alpha[e];
//                    alpha[e] = 1;
//                } else if (sg[u] < sg[v]) {
//                    r[u] -= alpha[e];
//                    r[v] += alpha[e];
//                    alpha[e] = 0;
//                }
//            }
//        }
//        double min_r = r[slt_nodes[0]];
//        for (int j = 0; j < cur; j++) {
//            min_r = min(min_r, r[slt_nodes[j]]);
//        }
//        double max_r = r[slt_nodes[cur]];
//        for (int j = cur; j < slt_nodes.size(); j++) {
//            max_r = max(max_r, r[slt_nodes[j]]);
//        }
//        printf("%d %.4f %.4f\n", i, min_r, max_r);
//        if (min_r > max_r) {
//            valid[i] = true;
//        } else {
//            valid[i] = false;
//            while (!q.empty()) {
//                auto tmp = q.front(); q.pop();
//                int u = edges[tmp.first].first, v = edges[tmp.first].second;
//                r[u] += tmp.second - alpha[tmp.first];
//                r[v] -= tmp.second - alpha[tmp.first];
//                alpha[tmp.first] = tmp.second;
//            }
//        }
//    }
//
//    check_first = (nsg == 1) || valid[0];
//    //merge stable groups
//    if (nsg > 1) {
//        vector<int> n_nag;
//        for (int i = 0; i < nsg; i++) {
//            if (i == 0 || valid[i - 1]) {
//                n_nag.push_back(nag[i]);
//            } else {
//                n_nag[n_nag.size() - 1] += nag[i];
//            }
//        }
//        nag = n_nag;
//
//        cur = 0;
//        nsg = nag.size();
//        double minr = m;
//        for (int i = 0; i < nsg; i++) {
//            printf("nsg %d %d ", i, nag[i]);
//            double tmp_r = m;
//            for (int j = cur; j < cur + nag[i]; j++) {
//                sg[slt_nodes[j]] = i;
//                tmp_r = min(tmp_r, r[slt_nodes[j]]);
//                minr = min(minr, r[slt_nodes[j]]);
//            }
//            printf("%.4f %.4f\n", minr, tmp_r);
//            cur += nag[i];
//        }
//    }
//    printf("updated nsg %d\n", nsg);
//
//}

//void Graph::check_sg() {
//    sort(slt_edges.begin(), slt_edges.end(), [this](int a, int b)->bool {
//        int a1 = min(sg[edges[a].first], sg[edges[a].second]);
//        int a2 = max(sg[edges[a].first], sg[edges[a].second]);
//        int b1 = min(sg[edges[b].first], sg[edges[b].second]);
//        int b2 = max(sg[edges[b].first], sg[edges[b].second]);
//        if (a1 != b1)
//            return a1 < b1;
//        else
//            return a2 < b2;
//    });
//
//    vector<vector<int>::iterator> its;
//    auto it = slt_edges.begin();
//
//    vector<double> max_r(nsg);
//    int cur = 0;
//    for (int i = 0; i < nsg; i++) {
//        its.push_back(it);
//        while (it != slt_edges.end() && min(sg[edges[*it].first], sg[edges[*it].second]) <= i) it++;
//
//        max_r[i] = r[slt_nodes[cur]];
//        double tmp_min = r[slt_nodes[cur]];
//        for (int j = cur + 1; j < cur + nag[i]; j++) {
//            max_r[i] = max(max_r[i], r[slt_nodes[j]]);
//            tmp_min = min(tmp_min, r[slt_nodes[j]]);
//        }
////        printf("%d %d %.4f %.4f\n", i, cur, max_r[i], tmp_min);
//        cur += nag[i];
//    }
//
//    vector<bool> valid(nsg);
//
//    double min_r = r[slt_nodes[0]];
//    cur = 0;
//
//    for (int i = 0; i < nsg - 1; i++) {
////        printf("i %d\n", i);
//        printf("%d %d %.4f %.4f\n", i, cur, min_r, max_r[i + 1]);
//        for (int j = cur; j < cur + nag[i]; j++) {
//            min_r = min(min_r, r[slt_nodes[j]]);
//        }
//        printf("%d %d %.4f %.4f\n", i, cur, min_r, max_r[i + 1]);
//        cur += nag[i];
//        vector<double> tmp_max_r(max_r.begin() + i + 1, max_r.end());
//        double mmax = *max_element(begin(tmp_max_r), end(tmp_max_r));
//        double mmin = min_r;
//        stack<int> s_alpha;
//        stack<int> s_pos;
//        valid[i] = true;
//        for (int j = 0; j <= i; j++) {
//            while (its[j] != slt_edges.end() && min(sg[edges[*its[j]].first], sg[edges[*its[j]].second]) <= j) {
//                if (max(sg[edges[*its[j]].first], sg[edges[*its[j]].second]) > i) {
//                    s_alpha.push(alpha[*its[j]]);
//                    s_pos.push(j);
//                    int u = edges[*its[j]].first, v = edges[*its[j]].second;
//                    if (sg[u] > sg[v]) {
//                        r[u] += 1 - alpha[*its[j]];
//                        max_r[sg[u]] = max(max_r[sg[u]], r[u]);
//                        mmax = max(mmax, r[u]);
//                        r[v] -= 1 - alpha[*its[j]];
//                        mmin = min(mmin, r[v]);
//                        alpha[*its[j]] = 1;
//                    } else if (sg[u] < sg[v]) {
//                        r[u] -= alpha[*its[j]];
//                        mmin = min(mmin, r[u]);
//                        r[v] += alpha[*its[j]];
//                        max_r[sg[v]] = max(max_r[sg[v]], r[v]);
//                        mmax = max(mmax, r[v]);
//                        alpha[*its[j]] = 0;
//                    }
//
//                }
//                its[j]++;
//                if (mmin <= mmax) {
//                    valid[i] = false;
//                    break;
//                }
//            }
//            if (!valid[i]) break;
//        }
//        printf("%d ", i);
//        printf(valid[i] ? "true\n" : "false\n");
//        if (valid[i]) {
//            min_r = min(min_r, mmin);
//        } else {
//            for (int j = i + 1; j < max_r.size(); j++) {
//                max_r[j] = tmp_max_r[j - i - 1];
//            }
//            while (!s_alpha.empty()) {
//                double val = s_alpha.top(); s_alpha.pop();
//                auto j = s_pos.top(); s_pos.pop();
//                its[j]--;
//                int u = edges[*its[j]].first, v = edges[*its[j]].second;
//                r[u] += val - alpha[*its[j]];
//                r[v] -= val - alpha[*its[j]];
//                alpha[*its[j]] = val;
//            }
//        }
//        printf("%d %.4f %.4f %.4f %.4f\n", i, min_r, mmin, mmax, max_r[i + 1]);
//    }
//
//    check_first = (nsg == 1) || valid[0];
//    //merge stable groups
//    if (nsg > 1) {
//        vector<int> n_nag;
//        for (int i = 0; i < nsg; i++) {
//            if (i == 0 || valid[i - 1]) {
//                n_nag.push_back(nag[i]);
//            } else {
//                n_nag[n_nag.size() - 1] += nag[i];
//            }
//        }
//        nag = n_nag;
//
//        cur = 0;
//        nsg = nag.size();
//        double minr = m;
//        for (int i = 0; i < nsg; i++) {
//            printf("nsg %d %d ", i, nag[i]);
//            double tmp_r = m;
//            for (int j = cur; j < cur + nag[i]; j++) {
//                sg[slt_nodes[j]] = i;
//                tmp_r = min(tmp_r, r[slt_nodes[j]]);
//                minr = min(minr, r[slt_nodes[j]]);
//            }
//            printf("%.4f %.4f\n", minr, tmp_r);
//            cur += nag[i];
//        }
//    }
//    printf("updated nsg %d\n", nsg);
//}

//void Graph::check_sg() {
//    vector<double> min_r(nsg);
//    vector<double> max_r(nsg);
//    int cur = 0;
////    for (int i = 0; i < nsg; i++) {
////        min_r[i] = r[slt_nodes[cur]];
////        max_r[i] = r[slt_nodes[cur]];
////        for (int j = cur + 1; j < cur + nag[i]; j++) {
////            min_r[i] = min(min_r[i], r[slt_nodes[j]]);
////            max_r[i] = max(max_r[i], r[slt_nodes[j]]);
////        }
////        cur += nag[i];
////        printf("i %d min %.4f max %.4f\n", i, min_r[i], max_r[i]);
////        if (i > 0) min_r[i] = min(min_r[i], min_r[i - 1]);
////    }
//
//    for (auto e : slt_edges) {
//        int u = edges[e].first;
//        int v = edges[e].second;
//        if (sg[u] > sg[v]) {
//            r[u] += 1 - alpha[e];
//            r[v] -= 1 - alpha[e];
//            alpha[e] = 1;
//        } else if (sg[u] < sg[v]) {
//            r[u] -= alpha[e];
//            r[v] += alpha[e];
//            alpha[e] = 0;
//        }
//    }
//
////    vector<double> min_r(nsg);
////    vector<double> max_r(nsg);
//    cur = 0;
//    for (int i = 0; i < nsg; i++) {
//        min_r[i] = r[slt_nodes[cur]];
//        max_r[i] = r[slt_nodes[cur]];
//        for (int j = cur + 1; j < cur + nag[i]; j++) {
//            min_r[i] = min(min_r[i], r[slt_nodes[j]]);
//            max_r[i] = max(max_r[i], r[slt_nodes[j]]);
//        }
//        cur += nag[i];
//        printf("i %d min %.4f max %.4f\n", i, min_r[i], max_r[i]);
//        if (i > 0) min_r[i] = min(min_r[i], min_r[i - 1]);
//    }
////    for (int i = 0; i < n; i++) {
////        printf("%.4f ", r[i]);
////    }
////    printf("\n");
//
//    for (int i = nsg - 2; i >= 0; i--) {
//        max_r[i] = max(max_r[i], max_r[i + 1]);
//    }
//
//    for (int i = 0; i < nsg; i++) {
//        printf("min %.4f max %.4f\n", min_r[i], max_r[i]);
//    }
//
//    vector<bool> valid(nsg);
//    for (int i = 0; i < nsg - 1; i++) {
//        valid[i] = min_r[i] > max_r[i + 1];
//    }
//    check_first = (nsg == 1) || valid[0];
//
//    //merge stable groups
//    if (nsg > 1) {
//        vector<int> n_nag;
//        for (int i = 0; i < nsg; i++) {
//            if (i == 0 || valid[i - 1]) {
//                n_nag.push_back(nag[i]);
//            } else {
//                n_nag[n_nag.size() - 1] += nag[i];
//            }
//        }
//        nag = n_nag;
//
//        cur = 0;
//        nsg = nag.size();
//        for (int i = 0; i < nsg; i++) {
//            for (int j = cur; j < cur + nag[i]; j++) {
//                sg[slt_nodes[j]] = i;
//            }
//            cur += nag[i];
//        }
//    }
//    printf("updated nsg %d\n", nsg);
//}

void Graph::pruning() {  //剪枝的算法
    vector<double> min_r(nsg);
    vector<double> max_r(nsg);

    int cur = 0;
    for (int i = 0; i < nsg; i++) {
        min_r[i] = r[slt_nodes[cur]];
        max_r[i] = r[slt_nodes[cur]];
        for (int j = cur + 1; j < cur + nag[i]; j++) {
            min_r[i] = min(min_r[i], r[slt_nodes[j]]);
            max_r[i] = max(max_r[i], r[slt_nodes[j]]);
        }
        for (int j = cur; j < cur + nag[i]; j++) {
            selected[slt_nodes[j]] = true;
            deg[slt_nodes[j]] = 0;
            rho_u[slt_nodes[j]] = min(rho_u[slt_nodes[j]], max_r[i]);
            rho_l[slt_nodes[j]] = max(rho_l[slt_nodes[j]], min_r[i]);
            if (rho_u[slt_nodes[j]] < rho_l[slt_nodes[j]]) {
                selected[slt_nodes[j]] = false;
            }
            if (active[slt_nodes[j]]) {
                rho_gu[slt_nodes[j]] = min(rho_gu[slt_nodes[j]], max_r[i]); 
            }
        }
        cur += nag[i];
    }


    // 这一段应该怎么改？
    for (auto e : slt_edges) {
        int u = edges[e].first;
        int v = edges[e].second;
        if (sg[u] > sg[v]) {
            selected[u] = false;
        }
        if (sg[u] < sg[v]) {
            selected[v] = false;
        }
    }

    for (auto u : slt_nodes) {
        if (selected[u]) {
            for (auto v : adj[u]) {
                if (rho_l[v] > rho_u[u]) {
                    selected[u] = false;
                }
            }
        }
    }

    // 计算core改为计算h-clique core
   /* for (auto e : slt_edges) {
        int u = edges[e].first;
        int v = edges[e].second;
        if (selected[u] && selected[v]) {
            ++deg[u];
            ++deg[v];
        }
    }*/
    
    for (auto& hc : slt_h_cliques) {
        int flag = 1;
        for (auto& hc_node : h_cliques[hc]) {
            if (!selected[hc_node]) {
                flag = 0;
                break;
            }
        }
        if (flag) {
            for (auto& hc_node : h_cliques[hc]) {
                ++deg[hc_node];
            }
        }  
    }

    


    queue<int> q;
    for (auto u : slt_nodes) {
        if (selected[u] && deg[u] < rho_l[u]) {
            selected[u] = false;
            q.push(u);
        }
    }

    while (!q.empty()) {
        int u = q.front(); q.pop();
        for (auto v : adj[u]) {
            if (selected[v]) {
                if (--deg[v] < rho_l[v]) {
                    selected[v] = false;
                    q.push(v);
                }
            }
        }
    }
    vector<int> tmp_nodes;
    vector<bool> inactive_sg(nsg, false);
    for (auto u : slt_nodes) {
        if (selected[u])
            tmp_nodes.push_back(u);
        else
            inactive_sg[sg[u]] = true;
    }
    slt_nodes = tmp_nodes;

    for (auto u : slt_nodes) {
        if (inactive_sg[sg[u]]) {
            active[u] = false;
        }
    }

    vector<int> tmp_edges;
    for (auto e : slt_edges) {
        if (selected[edges[e].first] && selected[edges[e].second]) {
            tmp_edges.push_back(e);
        }
    }
    slt_edges = tmp_edges;
    sort(slt_edges.begin(), slt_edges.end(), [this](int a, int b)->bool {
        return sg[edges[a].first] < sg[edges[b].first];
    });

    while (slt_nodes.size() > 0 && sg[slt_nodes.back()] > 0) {
        int n_nodes = slt_nodes.size() - 1;
        while (n_nodes > 0 && sg[slt_nodes[n_nodes]] == sg[slt_nodes.back()]) {
            --n_nodes;
        }
        n_nodes++;
        vector<int> t_nodes(slt_nodes.begin() + n_nodes, slt_nodes.end());
        stk_nodes.push(t_nodes);
        slt_nodes.resize(n_nodes);

        if (sg[t_nodes[0]] > sg[edges[slt_edges.back()].first]) {
            stk_nodes.pop();
            continue;
        }

        int n_edges = slt_edges.size() - 1;
        while (n_edges > 0 && sg[edges[slt_edges[n_edges]].first] == sg[edges[slt_edges.back()].first]) {
            --n_edges;
        }
        n_edges++;
        vector<int> t_edges(slt_edges.begin() + n_edges, slt_edges.end());
        stk_edges.push(t_edges);
        slt_edges.resize(n_edges);
        printf("sg %d %d %lu %lu\n", sg[t_nodes[0]], sg[edges[t_edges[0]].first], t_nodes.size(), t_edges.size());
        stk_CT.push(CT);
    }
}

void Graph::findLDS() {
   
    for (int i = 0; i < n; i++) {
        slt_nodes.push_back(i);
    }
    for (int i = 0; i < m; i++) {
        slt_edges.push_back(i);
    }
    CT = 0;
    h = 3;
    double fw_time = 0;   
    double sg_time = 0;
    double pr_time = 0;
    double mf_time = 0;
    int i = 0;

    clock_t start = clock();
    for (int i = 0; i < n; i++) {
        v2cliques.push_back({});
    }
 

    enumerateKCliques(h);
    compute_h_clique_core();
    prune_by_core();

    //while (!slt_nodes.empty() || !stk_nodes.empty()) {
    //std::cout << "Iteration: " << i++ << "  " << "slt_nodes.size(): " << slt_nodes.size() << "  " << "stk_nodes.size() : " << stk_nodes.size() << std::endl;
   
   /* if (slt_nodes.empty()) {
        slt_nodes = stk_nodes.top(); stk_nodes.pop();
        slt_edges = stk_edges.top(); stk_edges.pop();
        CT = stk_CT.top(); stk_CT.pop();
    }*/
    frank_wolfe_h_clique();
    CT++;
    while (CT <= 8) {
        std::cout << "Iteration: " << CT << std::endl;
        //frank_wolfe();
        frank_wolfe_h_clique(); //frank_wolfe Algorithm. 计算(r,α),用于寻找最大密度子图 
        clock_t t_fw = clock();
        fw_time += double(t_fw - start) / CLOCKS_PER_SEC;
        printf("fw time: %.4f\n", double(t_fw - start) / CLOCKS_PER_SEC);
        CT <<= 1;
        CT += NT;
        pava_h_clique();  //Pool Adjacent Violators Algorithm. 把图分解成稳定群的算法
        clock_t t_pv = clock();
        printf("pava time: %.4f\n", double(t_pv - t_fw) / CLOCKS_PER_SEC);
        check_sg_h_clique();  
        clock_t t_check_sg = clock();
        sg_time += double(t_check_sg - t_fw) / CLOCKS_PER_SEC;
        printf("check sg time: %.4f\n", double(t_check_sg - t_pv) / CLOCKS_PER_SEC);
        pruning();  //pruning Algorithm. 两部分剪枝操作
        clock_t t_prune = clock();
        pr_time += double(t_prune - t_check_sg) / CLOCKS_PER_SEC;
        printf("pruning time: %.4f\n", double(t_prune - t_check_sg) / CLOCKS_PER_SEC);
        if (!slt_nodes.empty() && check_first) {          
            double g = (double) slt_edges.size() / slt_nodes.size();
            vector<pair<int, int>> tmp_edges;
            for (auto e : slt_edges) {
                tmp_edges.push_back(edges[e]);
            }
            //TODO check by edge number? and connected component
            FlowNetwork fn = FlowNetwork(tmp_edges, g);
            double max_flow = fn.get_maxflow(0, fn.n-1);
            std::cout << "abs(max_flow - slt_edges.size()): " << abs(max_flow - slt_edges.size()) << std::endl;
            if (abs(max_flow - slt_edges.size()) <= 1e-3) {
                connected_components();
                int cur_u = 0;
                int cur_e = 0;
                for (auto pr : cmpt) {
                    vector<int> tmp_nodes(slt_nodes.begin() + cur_u, slt_nodes.begin() + pr.first);
                    printf("ldses candidate: #nodes %lu #edges %d\n", tmp_nodes.size(), pr.second - cur_e);
                    if (verify_LDS(tmp_nodes, g)) {     //verify_LDSAlgorithm. 验证是否是LDS
                        ldses.push_back(tmp_nodes);
                        lds_rho.push_back(g);
                        if (ldses.size() >= topk)
                            break;
                    }
                    cur_u = pr.first;
                    cur_e = pr.second;
                }
//                    ldses.push_back(slt_nodes);
                if (ldses.size() >= topk)
                    break;
                slt_nodes.clear();
                slt_edges.clear();
            }
        }
        clock_t t_verify_LDS = clock();
        mf_time += double(t_verify_LDS - t_prune) / CLOCKS_PER_SEC;
        printf("verifyLDS time: %.4f\n", double(t_verify_LDS - t_prune) / CLOCKS_PER_SEC);
    }

    printf("fw %.4f sec, sg %.4f sec, pr %.4f sec, mf %.4f sec\n", fw_time, sg_time, pr_time, mf_time);

}


void Graph::compute_h_clique_core() {
    max_d = 0;
    for (int i = 0; i < h_cliques.size(); i++) {
        for (auto& hc_node : h_cliques[i]) {
            ++deg[hc_node];
        }
    }

    for (int i = 0; i < n; i++) {
        max_d = max(deg[i], max_d);
    }

    printf("max_d %d\n", max_d);
    pos.resize(n);

    vector<int> sorted_nodes;

    for (int i = 0; i < n; i++) {
        sorted_nodes.push_back(i);
    }

    
    sort(sorted_nodes.begin(), sorted_nodes.end(), [this](int a, int b)->bool {
        return deg[a] < deg[b];
        });


 
    for (int i = 0; i < n; i++) {
        pos[sorted_nodes[i]] = i;
    }
   
  
    vector<int> vtx;
    
    while (!sorted_nodes.empty()) {
        int min_deg = deg[sorted_nodes[0]];
        int v = sorted_nodes.front();
        if (deg[v] == min_deg) {
            core[v] = deg[v];
        }
        vtx.push_back(v);
        for (int i = 0; i < v2cliques[v].size(); i++) {
            vector<int> hc = h_cliques[v2cliques[v][i]];
            for (int j = 0; j < hc.size(); j++) {
                int u = hc[j];
                if (deg[u] > deg[v]) {
                    deg[u]--;
                }
            }
        }
        sorted_nodes.erase(sorted_nodes.begin());

        sort(sorted_nodes.begin(), sorted_nodes.end(), [this](int a, int b)->bool {
            return deg[a] < deg[b];
        });

        
    }

    slt_nodes.clear();
    slt_edges.clear();

    for (int i = 0; i < n; i++) {
        if (selected[i]) slt_nodes.push_back(i);
    }
    for (int i = 0; i < m; i++) {
        if (selected[edges[i].first] && selected[edges[i].second]) {
            slt_edges.push_back(i);
        }
    }
    sort(slt_nodes.begin(), slt_nodes.end(), [this](int a, int b)->bool {
        return deg[a] < deg[b];
    });

}

void Graph::compute_core() {
    max_d = 0;
    for (int i = 0; i < n; i++) {
        deg[i] = adj[i].size();
        max_d = max(deg[i], max_d);
    }
    printf("max_d %d\n", max_d);
    vector<int> bin(max_d + 1, 0);
    pos.resize(n);
    vector<int> vert(n);
    for (int i = 0; i < n; i++) {
        ++bin[deg[i]];
    }
    int start = 0;
    for (int d = 0; d <= max_d; d++) {
        int num = bin[d];
        bin[d] = start;
        start += num;
    }
    for (int i = 0; i < n; i++) {
        pos[i] = bin[deg[i]]++;
        vert[pos[i]] = i;
    }
    for (int d = max_d; d > 0; d--) {
        bin[d] = bin[d - 1];
    }
    bin[0] = 0;
    for (int i = 0; i < n; i++) {
        int u = vert[i];
        for (auto v : adj[u]) {
            if (deg[v] > deg[u]) {
                int dv = deg[v], pv = pos[v];
                int pw = bin[dv], w = vert[pw];
                if (v != w) {
                    pos[v] = pw; vert[pv] = w;
                    pos[w] = pv; vert[pw] = v;
                }
                ++bin[dv]; --deg[v];
            }
        }
    }
}

void Graph::compute_h_cliques() {

}

void Graph::prune_by_core() {
    //for (int u = 0; u < n; u++) {
    //    rho_l[u] = 0;
    //    rho_u[u] = INT_MAX;
    //    rho_gu[u] = deg[u];
    //    // TODO deg换成clique core
    //}
    for (int u = 0; u < n; u++) {
        rho_l[u] = core[u] / h;
        rho_u[u] = core[u];
        rho_gu[u] = core[u];
    }
    vector<double> tmp_rho_l(n);
    queue<int> q;
    for (int u = 0; u < n; u++) {
        tmp_rho_l[u] = rho_l[u];
        // LDSflow不一定适用于clique
        for (auto v : adj[u]) {
            tmp_rho_l[u] = max(tmp_rho_l[u], rho_l[v]);
        }
        if (tmp_rho_l[u] > rho_u[u] + DELTA){
            selected[u] = false;
            q.push(u);
        }
    }


    vector<int> vtx;
    while (!q.empty()) {
        int u = q.front(); q.pop();
        vtx.push_back(u);
        for (auto v : adj[u]) {
            if (selected[v] && pos[u] > pos[v]) {
                --deg[v];
                if (tmp_rho_l[v] > deg[v] + DELTA) {
                    selected[v] = false;
                    q.push(v);
                }
            }
        }
    }

    slt_nodes.clear();
    slt_edges.clear();
    vector<int> selected_cliques(h_cliques.size(),  1);
    for (int i = 0; i < n; i++) {
        if (selected[i]) slt_nodes.push_back(i);
        else if (!selected[i]) {
            for (int j = 0; j < v2cliques[i].size(); j++) {
                selected_cliques[v2cliques[i][j]] = 0;
            }
        }

    }
    for (int i = 0; i < m; i++) {
        if (selected[edges[i].first] && selected[edges[i].second]) {
            slt_edges.push_back(i);
        }
    } 

    for (int i = 0; i < n; i++) {
        
    }

    for (int i = 0; i < h_cliques.size(); i++) {
        if (selected_cliques[i]) {
            slt_h_cliques.push_back(i);
        }
    }
    printf("#slt node %lu #slt edge %lu #slt_h_cliques %lu\n", slt_nodes.size(), slt_edges.size(), slt_h_cliques.size());

    sort(vtx.begin(), vtx.end(), [this](int a, int b)->bool {
            return rho_gu[a] > rho_gu[b];
    });
    for (auto u : vtx) {
        if (active[u]) {
            active[u] = false;
            double threshold = rho_gu[u] + DELTA;
            q.push(u);
            while (!q.empty()) {
                int v = q.front(); q.pop();
                for (auto w : adj[v]) {
                    if (active[w] && rho_l[w] <= threshold) {
                        active[w] = false;
                        q.push(w);
                    }
                }
            }
        }
    }

    int cnt = 0;
    for (int i = 0; i < n; i++) {
        if (active[i]) ++cnt;
    }
    printf("#active nodes %d\n", cnt);
}

bool Graph::verify_LDS(vector<int> & nodes, double g) {   //验证是否是LDS
    for (auto u : nodes) {
        for (auto v : adj[u]) {
            if (rho_l[v] > g) {
                printf("validate failed\n");
                return false;
            }
        }
    }
    for (auto u : nodes) {
        lds_num[u] = ldses.size();
    }
    bool flag = true;


    ++num_verify;
    queue<int> q;
    vector<pair<int, int>> tmp_edges;
    for (auto u : nodes) {
        if (veri_vtx[u] != num_verify) {
            q.push(u);
            veri_vtx[u] = num_verify;
        }
        while (!q.empty()) {
            int v = q.front(); q.pop();
            for (auto w : adj[v]) {
//                if (slt_nodes.size() == 13 && slt_edges.size() == 68) printf("%d %d %.4f %.4f\n", v, w, rho_gu[w], rho_l[w]);
                if (fn_baseline) {
                    if (rho_gu[w] >= g) {
                        if (veri_vtx[w] != num_verify) {
                            if (lds_num[w] != -1 && lds_num[w] < lds_num[u]) {
                                flag = false;
                            }
                            veri_vtx[w] = num_verify;
                            q.push(w);
                        }
                        if (v < w)
                            tmp_edges.emplace_back(v, w);
                    }
                } else {
                    if (rho_gu[w] >= g) {
                        if (veri_vtx[w] != num_verify) {
                            if (lds_num[w] != -1 && lds_num[w] < lds_num[u]) {
                                flag = false;
                            }
//                        veri_vtx[w] = num_verify;
//                        q.push(w);
                            if (rho_l[w] <= g) {
                                veri_vtx[w] = num_verify;
                                q.push(w);
                            } else {
                                flag = false;
                                tmp_edges.emplace_back(v, v);
                            }
                        }
                        if (v < w && rho_l[w] <= g)
                            tmp_edges.emplace_back(v, w);
                    }
                }
            }
        }
    }
    printf("size of tmp edges %lu\n", tmp_edges.size());
//    if (nodes.size() == 8 && tmp_edges.size() == 22) {
//        for (auto u : nodes) {
//            printf("node %d\n", u);
//        }
//        for (auto e : tmp_edges) {
//            printf("edge %d %d\n", e.first, e.second);
//        }
//    }
    if (flag) return flag;

    flag = true;
    FlowNetwork fn = FlowNetwork(tmp_edges, g - 1.0 / n / n, true);
    vector<int> tmp_nodes;
    fn.get_mincut(0, fn.n - 1, tmp_nodes);
    ++num_verify;
    printf("size of tmp nodes %lu\n", tmp_nodes.size());
    for (auto u : tmp_nodes) {
//        printf("%d ", u);
        veri_vtx[u] = num_verify;
    }
    printf("\n");
    for (auto u : nodes) {
        for (auto v : adj[u]) {
            if (lds_num[v] != lds_num[u] && veri_vtx[v] == num_verify) {
                flag = false;
                break;
            }
        }
        if (!flag) break;
    }

    if (flag) return flag;
    printf("validate failed\n");

    for (auto u : nodes) {
        lds_num[u] = -1;
    }
    return false;
}

void Graph::output(char *ds_address) {
    printf("num of LDS %lu\n", ldses.size());
    FILE* dsFile = fopen(ds_address, "w");
    for (int i = 0; i < ldses.size(); i++) {

        fprintf(dsFile, "%lu %.4f\n", ldses[i].size(), lds_rho[i]);
        for (auto & u : ldses[i]) {
            fprintf(dsFile, "%d ", u);
        }
        fprintf(dsFile, "\n");
    }

    fclose(dsFile);
}

int Graph::find_fa(int x) {
    if (x != fa[x])
        fa[x] = find_fa(fa[x]);
    return fa[x];
//    return (x == fa[x]) ? x : (fa[x] = find_fa(fa[x]));
}

void Graph::connected_components() {
    for (auto u : slt_nodes) {
        fa[u] = u;
    }

    for (auto e : slt_edges) {
//        if (find_fa(edges[e].first) != find_fa(edges[e].second))
        int x = find_fa(edges[e].first);
        int y = find_fa(edges[e].second);
//        printf("%d %d %d %d\n", edges[e].first, edges[e].second, x, y);
        fa[x] = y;
    }
    for (auto u : slt_nodes) {
        find_fa(u);
    }

    sort(slt_nodes.begin(), slt_nodes.end(), [this](int a, int b)->bool {
        return fa[a] > fa[b];
    });
    sort(slt_edges.begin(), slt_edges.end(), [this](int a, int b)->bool {
        return fa[edges[a].first] > fa[edges[b].first];
    });

//    printf("fa ");
//    for (int i = 0; i < n; i++) {
//        printf("%d ", find_fa(i));
//    }
//    printf("\n");

    cmpt.clear();
    int x = 1, y = 1;
    while (x < slt_nodes.size() && y < slt_edges.size()) {
        while (x < slt_nodes.size() && fa[slt_nodes[x]] == fa[slt_nodes[x - 1]]) x++;
        while (y < slt_edges.size() && fa[edges[slt_edges[y]].first] == fa[edges[slt_edges[y - 1]].first]) y++;
        cmpt.emplace_back(x, y);
        ++x;
        ++y;
    }
//    for (auto pr : cmpt) {
//        printf("%d %d\n", pr.first, pr.second);
//    }
}









//
//  graph_skeletonize.cpp
//  MeshEditE
//
//  Created by Andreas Bærentzen on 26/01/2020.
//  Copyright © 2020 J. Andreas Bærentzen. All rights reserved.
//

#include <future>
#include <thread>
#include <unordered_set>
#include <queue>
#include <list>
#include <vector>
#include <iostream>
#include <random>
#include <chrono>
#include <forward_list>
#include <GEL/Util/AttribVec.h>
#include <GEL/Geometry/Graph.h>
#include <GEL/Geometry/graph_util.h>
#include <GEL/Geometry/DynCon.h>
#include <GEL/Geometry/graph_skeletonize.h>
#include <GEL/Geometry/graph_io.h>

using namespace std;
using namespace CGLA;
using namespace Util;
using namespace Geometry;

#ifndef MULTI_SHRINK
#define MULTI_SHRINK 0
#endif
#ifndef THICC_SEP
#define THICC_SEP 1
#endif
#ifndef DYNCON
#define DYNCON Treap
#endif

namespace Geometry {

    using NodeID = AMGraph::NodeID;
    using NodeSetUnordered = unordered_set<NodeID>;
    using NodeQueue = queue<NodeID>;
    using SepVec = vector<Separator>;

    void greedy_weighted_packing(const AMGraph3D &g, NodeSetVec &node_set_vec, bool normalize) {

        vector<pair<double, int>> node_set_index;

        if (normalize) {
            vector<double> opportunity_cost(node_set_vec.size(), 0.0);

            for (int i = 0; i < node_set_vec.size(); ++i) {
                const auto&[w_i, ns_i] = node_set_vec[i];
                for (int j = i + 1; j < node_set_vec.size(); ++j) {
                    const auto&[w_j, ns_j] = node_set_vec[j];
                    int matches = test_intersection(ns_i, ns_j);
                    if (matches > 0) {
                        opportunity_cost[i] += w_j;
                        opportunity_cost[j] += w_i;
                    }
                }
                double weight = w_i / opportunity_cost[i];
                node_set_index.push_back(make_pair(weight, i));
            }
        } else
            for (int i = 0; i < node_set_vec.size(); ++i) {
                const auto&[w_i, ns_i] = node_set_vec[i];
                node_set_index.push_back(make_pair(w_i, i));
            }

        sort(begin(node_set_index), end(node_set_index), greater<pair<double, int>>());
        NodeSetVec node_set_vec_new;
        AttribVec<NodeID, size_t> set_index(g.no_nodes(), -1);
        for (const auto&[norm_weight, ns_idx]: node_set_index) {
            const auto&[weight, node_set] = node_set_vec[ns_idx];
            bool immaculate = true;
            for (auto n: node_set)
                if (set_index[n] != -1) {
                    immaculate = false;
                    break;
                }
            if (immaculate) {
                node_set_vec_new.push_back(node_set_vec[ns_idx]);
                for (auto n: node_set)
                    set_index[n] = ns_idx;
            }
        }
        swap(node_set_vec_new, node_set_vec);
    }

    // Returns a vector of separators without duplicates.
    SepVec filter_duplicate_separators(const SepVec &separators) {
        // Works by inserting then extracting from a hashset.
        auto sep_hash = [](const Separator &a) {
            // The good
            size_t seed = 0;
            for (auto n: a.sigma) {
                seed = seed ^ hash<size_t>()(n);
            }
            return seed;
        };
        auto sep_equal = [](const Separator &a, const Separator &b) {
            for (auto n: a.sigma) {
                // We can do this only because a.second and b.second is sorted.
                if (b.sigma.count(n) == 0) {
                    return false;
                }
            }
            return true;
        };
        unordered_set<Separator, decltype(sep_hash), decltype(sep_equal)> separators_set(0, sep_hash, sep_equal);

        // Insert all elements into set.
        for (auto &sep: separators) {
            auto old_sep = separators_set.find(sep);
            if (old_sep == separators_set.end()) {
                separators_set.insert(sep);
            } else {
                // Update the level such that it is the lowest occurrence of the separator.
                old_sep->grouping = min(old_sep->grouping, sep.grouping);
            }
        }

        // Extract.
        SepVec filtered_separators;
        filtered_separators.reserve(separators_set.size());
        for (auto &sep: separators_set) {
            filtered_separators.push_back(sep);
        }
        return filtered_separators;
    }

    // Adds leniency to packing by allowing overlapped usage of vertices up to some capacity
    // Is otherwise the same as greedy_weighted_packing but uses a Separator vector instead of NodeSetVec.
    void capacity_packing(const AMGraph3D &g, SepVec &separator_vec, bool normalize,
                          const vector<size_t> &capacity) {

        vector<pair<double, int>> node_set_index;
        vector<NodeSet> ordered_seps;
        ordered_seps.reserve(separator_vec.size());
        for(auto & s : separator_vec){
            ordered_seps.push_back(order(s.sigma));
        }

        if (normalize) {
            vector<double> opportunity_cost(separator_vec.size(), 0.0);

            for (int i = 0; i < separator_vec.size(); ++i) {
                const double &w_i = separator_vec[i].quality;
                const auto &ns_i = ordered_seps[i];
                for (int j = i + 1; j < separator_vec.size(); ++j) {
                    const double &w_j = separator_vec[j].quality;
                    const auto &ns_j = ordered_seps[j];
                    int matches = test_intersection(ns_i, ns_j);
                    if (matches > 0) {
                        opportunity_cost[i] += w_j;
                        opportunity_cost[j] += w_i;
                    }
                }
                double weight = w_i / opportunity_cost[i];
                node_set_index.emplace_back(weight, i);
            }
        } else
            for (int i = 0; i < separator_vec.size(); ++i) {
                const double &w_i = separator_vec[i].quality;
                node_set_index.emplace_back(w_i, i);
            }

        sort(begin(node_set_index), end(node_set_index), greater<pair<double, int>>());
        SepVec node_set_vec_new;
        AttribVec<NodeID, size_t> set_index(g.no_nodes(), 0); // Counts usage
        for (const auto&[norm_weight, ns_idx]: node_set_index) {
            const auto &node_set = separator_vec[ns_idx].sigma;
            bool immaculate = true;
            for (auto n: node_set)
                if (set_index[n] + 1 > capacity[n]) {
                    immaculate = false;
                    break;
                }
            if (immaculate) {
                node_set_vec_new.push_back(separator_vec[ns_idx]);
                for (auto n: node_set)
                    set_index[n]++;
            }
        }
        swap(node_set_vec_new, separator_vec);
    }

    // Samples vertices from a graph that are likely to create nice
    // separators when a separator is grown from the vertex
    // by growing restricted separators on a multi_scale graph.
    // by using sampling=true, restricted separators are only grown from a subset of vertices in the multi-scale graph.
    std::vector<NodeID> multi_scale_vertex_sampling(
            AMGraph3D &g,
            double quality_noise_level,
            int optimization_steps,
            int restricted_separator_threshold,
            bool sampling = true) {

        const int CORES = thread::hardware_concurrency();
        vector<thread> threads(CORES);

        Util::AttribVec<NodeID, uint> touched(g.no_nodes(), 0); // Used for internal sampling.

        // Generate a multi-scale graph.
        auto msg = multiscale_graph(g, restricted_separator_threshold, false);

        // Collection of vertices where successfully grew a restricted separator on the multi-scale graph converted to
        // vertices on the g.
        // Keep a vector for each thread.
        vector<vector<NodeID>> successful_starting_vertex_vv(CORES);

        // Function for growing a single restricted separators and converting successes to input vertices.
        auto sample_starting_vertex = [&](int core,
                                          const AMGraph3D &current_g,
                                          const vector<vector<NodeID>> &exp_map) {
            auto &successful_starting_vertex_v = successful_starting_vertex_vv[core];
            for (auto n: current_g.node_ids()) {
                double probability = 1.0 / int_pow(2.0, touched[n]);
                if (n % CORES == core && (!sampling || rand() <= probability * RAND_MAX)) {
                    Separator separator = local_separator(current_g, n, quality_noise_level,
                                                          optimization_steps,
                                                          restricted_separator_threshold);
                    const auto &sigma = separator.sigma;
                    if (!sigma.empty()) {
                        // Touch each vertex for sampling.
                        NodeSetUnordered sigma_unordered;
                        if (sampling) {
                            for (auto i: sigma) {
                                touched[i]++;
                            }
                        }

                        // Take the position we began from. Find the closest vertex from the expanded set of vertices.
                        // The expanded vertices are vertices on g.
                        NodeID n0 = exp_map[n][0];
                        const auto &n_pos = current_g.pos[n]; // Position of the node we grew from.
                        double dist_to_n0 = abs(sqrt(
                                pow((n_pos[0] - g.pos[n0][0]), 2) +
                                pow((n_pos[1] - g.pos[n0][1]), 2) +
                                pow((n_pos[2] - g.pos[n0][2]), 2)));
                        // Of the expanded nodes, find the one closest.
                        for (uint i = 1; i < exp_map[n].size(); ++i) {
                            const auto &candidate_n0 = exp_map[n][i];
                            const auto &candidate_n0_pos = g.pos[candidate_n0];
                            double dist = abs(sqrt(
                                    pow((n_pos[0] - candidate_n0_pos[0]), 2) +
                                    pow((n_pos[1] - candidate_n0_pos[1]), 2) +
                                    pow((n_pos[2] - candidate_n0_pos[2]), 2)));
                            if (dist < dist_to_n0) {
                                dist_to_n0 = dist;
                                n0 = candidate_n0;
                            }
                        }
                        successful_starting_vertex_v.emplace_back(n0);
                    }
                }
            }
        };

        // Found vertices are eventually inserted into a set to filter duplicates.
        auto seed_compare = [](const NodeID &a, const NodeID &b) {
            // This is used when growing from static centre so the centre can be disregarded.
            return a < b;
        };
        set<NodeID, decltype(seed_compare)> successful_starting_vertex_set(seed_compare);


        // Now compute restricted separators for each layer.
        for (auto layer = 0; layer < msg.layers.size(); ++layer) {
            const auto &g_current = msg.layers[layer];
            const auto &exp_map_current = msg.expansion_map_vec[layer];

            for (int i = 0; i < CORES; ++i)
                threads[i] = thread(sample_starting_vertex, i, g_current, exp_map_current);
            for (int i = 0; i < CORES; ++i)
                threads[i].join();

            // Cleanup touched.
            if (sampling) {
                for (uint i = 0; i < g_current.no_nodes(); ++i) {
                    touched[i] = 0;
                }
            }

            // Unpack
            for (const auto &thread_results: successful_starting_vertex_vv) {
                for (auto vertex: thread_results) {
                    successful_starting_vertex_set.insert(vertex);
                }
            }
        }

        // Convert the sampled vertices pack into a vector.
        vector<NodeID> sampled_vertices;
        sampled_vertices.reserve(successful_starting_vertex_set.size());
        for (auto vertex: successful_starting_vertex_set) {
            sampled_vertices.push_back(vertex);
        }
        return sampled_vertices;
    }


    NodeSetVec maximize_node_set_vec(AMGraph3D &g, const NodeSetVec &_node_set_vec) {
        NodeSetVec node_set_vec = _node_set_vec;

        BreadthFirstSearch bfs(g);
        AttribVec<NodeID, int> nsv_membership(g.no_nodes(), -1);
        for (int nsv_cnt = 0; nsv_cnt < node_set_vec.size(); ++nsv_cnt) {
            const auto &nsv = node_set_vec[nsv_cnt];
            for (auto n: nsv.second) {
                bfs.add_init_node(n);
                nsv_membership[n] = nsv_cnt;
            }
        }

        while (bfs.Dijkstra_step());

        for (auto n: g.node_ids())
            if (nsv_membership[n] == -1 && bfs.pred[n] != AMGraph::InvalidNodeID) {
                auto m = n;
                vector<NodeID> path;
                while (nsv_membership[m] == -1) {
                    path.push_back(m);
                    m = bfs.pred[m];
                }
                auto nsv_number = nsv_membership[m];
                for (auto l: path)
                    nsv_membership[l] = nsv_number;
            }

        for (auto n: g.node_ids())
            if (nsv_membership[n] != -1) {
                node_set_vec[nsv_membership[n]].second.insert(n);
            }
        return node_set_vec;
    }


    pair<AMGraph3D, Util::AttribVec<AMGraph::NodeID, AMGraph::NodeID>>
    skeleton_from_node_set_vec(AMGraph3D &g, const NodeSetVec &_node_set_vec, bool merge_branch_nodes,
                               int smooth_steps) {
        // First expand the node_set_vec so that all nodes are assigned.
        NodeSetVec node_set_vec = maximize_node_set_vec(g, _node_set_vec);
        //    color_graph_node_sets(g, node_set_vec);
        //    return make_pair(g, AttribVec<NodeID, NodeID> ());

        // Skeleton graph
        AMGraph3D skel;


        Util::AttribVec<AMGraph::NodeID, double> node_size;

        // Map from g nodes to skeleton nodes
        AttribVec<NodeID, NodeID> skel_node_map(g.no_nodes(), AMGraph::InvalidNodeID);

        // Map from skeleton node to its weight.
        AttribVec<NodeID, double> skel_node_weight;

        // Create a skeleton node for each node set.
        for (const auto&[w, ns]: node_set_vec)
            if (ns.size() > 0) {
                const NodeID skel_node = skel.add_node(Vec3d(0));
                Vec3d avg_pos(0);
                for (auto n: ns) {
                    avg_pos += g.pos[n];
                    skel_node_map[n] = skel_node;
                }
                avg_pos /= ns.size();

                vector<double> lengths;
                for (auto n: ns)
                    lengths.push_back(length(g.pos[n] - avg_pos));
                nth_element(begin(lengths), begin(lengths) + lengths.size() / 2, end(lengths));
                node_size[skel_node] = lengths[lengths.size() / 2];
                skel.pos[skel_node] = avg_pos;
                skel_node_weight[skel_node] = (ns.size());
            }

        // If two graph nodes are connected and belong to different skeleton nodes,
        // we also connect their respective skeleton nodes.
        for (NodeID n0: g.node_ids())
            for (NodeID m: g.neighbors(n0)) {
                NodeID skel_node_n0 = skel_node_map[n0];
                NodeID skel_node_m = skel_node_map[m];
                if (skel_node_m != skel_node_n0) {
                    skel.connect_nodes(skel_node_n0, skel_node_m);
                }
            }

        // At this point, we return if the merging of branch nodes is not desired.
        if (!merge_branch_nodes)
            return make_pair(skel, skel_node_map);

        // If skeletal nodes s0, s1, and s2 form a clique, we add them to the cliques
        // vector of NodeSets.
        vector<NodeSet> cliques;
        for (NodeID s0: skel.node_ids()) {
            auto N_s0 = skel.neighbors(s0);
            for (NodeID s1: N_s0)
                for (NodeID s2: N_s0)
                    if (s1 != s2 && skel.find_edge(s1, s2) != AMGraph::InvalidEdgeID)
                        cliques.push_back({s0, s1, s2});
        }

        // If two cliques intersect with more than a single node, we join them.
        for (int i = 0; i < cliques.size(); ++i)
            for (int j = 0; j < cliques.size(); ++j)
                if (i != j) {
                    if (test_intersection(cliques[i], cliques[j]) > 1) {
                        cliques[i].insert(begin(cliques[j]), end(cliques[j]));
                        cliques[j].clear();
                    }
                }

        // Now, we create a branch node connected to all of the nodes in the
        // merged clique
        vector<NodeID> branch_nodes;
        for (auto &ns: cliques)
            if (!ns.empty()) {
                Vec3d avg_pos(0);
                double wsum = 0;
                double rad = 0;
                for (auto n: ns) {
                    avg_pos += skel_node_weight[n] * skel.pos[n];
                    rad += skel_node_weight[n] * node_size[n];
                    wsum += skel_node_weight[n];
                }
                avg_pos /= wsum;
                rad /= wsum;
                auto n_branch = skel.add_node(avg_pos);
                branch_nodes.push_back(n_branch);
                skel.node_color[n_branch] = Vec3f(1, 0, 0);
                node_size[n_branch] = rad;
                skel_node_weight[n_branch] = wsum / ns.size();
                for (auto n: ns)
                    skel.connect_nodes(n_branch, n);
            }


        // Disconnect all of the nodes that are now connected to a
        // common branch node.
        for (auto n: branch_nodes) {
            const auto &N = skel.neighbors(n);
            for (auto nn: N)
                for (auto nm: N)
                    skel.disconnect_nodes(nn, nm);
        }

        // Smooth gently
        for (int iter = 0; iter < smooth_steps; ++iter) {
            auto skel_new_pos = skel.pos;
            for (auto sn: skel.node_ids()) {
                skel_new_pos[sn] = Vec3d(0);
                double w_sum = 0;
                for (auto nsn: skel.neighbors(sn)) {
                    double w = sqrt(skel_node_weight[nsn]) / skel.neighbors(nsn).size();
                    skel_new_pos[sn] += w * skel.pos[nsn];
                    w_sum += w;
                }
                skel_new_pos[sn] /= w_sum;
            }

            for (auto sn: skel.node_ids()) {
                double w = 1.0 / skel.neighbors(sn).size();
                skel.pos[sn] = skel.pos[sn] * w + (1.0 - w) * skel_new_pos[sn];
            }
        }

        // Finally, store the node size in the green channel of the node color
        // it is perhaps not the best idea, but this way we do not need another
        // way of storing the size....
        for (auto n: skel.node_ids())
            skel.node_color[n][1] = node_size[n];

        return make_pair(skel, skel_node_map);
    }

    AttribVec<NodeID, double> junction_distance(const AMGraph3D &g) {
        BreadthFirstSearch bfs(g);
        for (auto n: g.node_ids()) {
            if (g.neighbors(n).size() > 2)
                bfs.add_init_node(n, 0);
        }
        while (bfs.Dijkstra_step());
        return bfs.dist;
    }

    NodeSetVec skeletal_reweighting(AMGraph3D &g, const NodeSetVec &nsv_for_skel) {

        auto[skel, _] = skeleton_from_node_set_vec(g, nsv_for_skel, true, 0);
        auto leaf_dist = junction_distance(skel);
        NodeSetVec nsv;
        for (int i = 0; i < nsv_for_skel.size(); ++i) {
            const auto&[w, ns] = nsv_for_skel[i];
            double l = leaf_dist[NodeID(i)];
            nsv.push_back(make_pair(sqrt(l + 1) * w, ns));
        }
        return nsv;
    }

    NodeSetVec separating_node_sets(AMGraph3D &g, const AttribVec<NodeID, double> &dist, int shift) {

        BreadthFirstSearch bfs(g, dist);
        while (bfs.step());
        vector<pair<int, NodeID>> nodes_by_tin;

        for (auto n: g.node_ids())
            nodes_by_tin.push_back(make_pair(bfs.T_in[n], n));
        //    sort(begin(nodes_by_tin), end(nodes_by_tin));
        shuffle(begin(nodes_by_tin), end(nodes_by_tin), default_random_engine(rand()));


        vector<vector<NodeID>> separators;
        AttribVec<NodeID, int> separator_idx(g.no_nodes(), -1);
        int first_T0 = shift;
        for (const auto&[T0, n0]: nodes_by_tin)
            if (/*T0 >= first_T0 &&*/ separator_idx[n0] == -1) {
                int new_sep_idx = separators.size();
                separator_idx[n0] = new_sep_idx;
                queue<NodeID> nq;
                nq.push(n0);

                bool intersects_previous = false;
                vector<NodeID> sep({n0});
                while (!nq.empty() && !intersects_previous) {
                    NodeID n = nq.front();
                    nq.pop();
                    for (auto nn: g.neighbors(n)) {
                        if (separator_idx[nn] == -1) {
                            int T_in = bfs.T_in[nn];
                            int T_out = bfs.T_out[nn];
                            if (T_in <= T0 && T0 < T_out) {
                                separator_idx[nn] = new_sep_idx;
                                sep.push_back(nn);
                                nq.push(nn);
                            }
                        } else if (separator_idx[nn] != new_sep_idx) {
                            intersects_previous = true;
                            break;
                        }
                    }
                }
                if (intersects_previous) {
                    for (auto n: sep)
                        separator_idx[n] = -1;
                } else
                    separators.push_back(sep);
            }

        NodeSetVec nsv_for_skel;
        for (const auto &nv: separators)
            if (nv.size() > 10) {
                NodeSet ns = NodeSet(begin(nv), end(nv));
                double c = vertex_separator_curvature(g, ns, bfs.T_out);
                nsv_for_skel.push_back(make_pair(1.0 / (1e-5 + c), ns));
            }

        return nsv_for_skel;
        //    return skeletal_reweighting(g,nsv_for_skel);
    }


    NodeSetVec front_separators(AMGraph3D &g, const vector<AttribVecDouble> &dvv) {
        auto process_dist = [](AMGraph3D &g, const AttribVecDouble &dist, int shift) -> NodeSetVec {
            auto node_set_vec = separating_node_sets(g, dist, shift);
            return node_set_vec;
        };

        size_t N = 50;//dvv.size();
        NodeSetVec node_set_vec_global;
        vector<future<NodeSetVec>> nsvfutures(N);
        
        for(int i=0;i<N;++i)
            nsvfutures[i] = async(launch::async, process_dist, ref(g), dvv[0], i);
        
        for(int i=0;i<N;++i) {
            NodeSetVec nsv =nsvfutures[i].get();
            node_set_vec_global.insert(end(node_set_vec_global), begin(nsv), end(nsv));
        }

        greedy_weighted_packing(g, node_set_vec_global, true);
        color_graph_node_sets(g, node_set_vec_global);
        return node_set_vec_global;
    }

    int find_component(const AMGraph3D &g, NodeID n, const vector<NodeSetUnordered> &front_components) {
        int component = -1;
        for (auto m: g.neighbors(n))
            for (int i = 0; i < front_components.size(); ++i)
                if (front_components[i].count(m)) {
                    if (component == -1)
                        component = i;
                    else if (component != i) {
                        component = -1;
                        return component;
                    }
                }
        return component;
    };


    template<typename T>
    void smooth_attribute(const AMGraph3D &g, AttribVec<NodeID, T> &attrib, const NodeSetUnordered &node_set,
                          int N_iter = 1, const AttribVec<NodeID, Vec3d> *_pos = 0) {
        double delta = 0.5;
        const AttribVec<NodeID, Vec3d> &pos = (_pos == 0) ? g.pos : *_pos;
        auto attrib_new = attrib;
        for (int iter = 0; iter < N_iter; ++iter) {
            for (auto n: node_set) {
                auto N = g.neighbors(n);
                attrib_new[n] = T(0);
                double w_sum = 0.0;
                for (auto m: N) {
                    double w = 1.0 / (1e-30 + length(pos[m] - pos[n]));
                    attrib_new[n] += w * attrib[m];
                    w_sum += w;
                }
                attrib_new[n] = ((1.0 - delta) * attrib[n] + delta * attrib_new[n] / w_sum);
            }
            swap(attrib_new, attrib);
        }
    }


    void node_set_thinning(const AMGraph3D &g, NodeSetUnordered &separator,
                           vector<NodeSetUnordered> &front_components,
                           const AttribVecDouble &priority) {
        using DN_pair = pair<double, NodeID>;
        priority_queue<DN_pair> DNQ;
        for (auto n: separator)
            DNQ.push(make_pair(priority[n], n));

        bool did_work = false;
        do {
            did_work = false;
            priority_queue<DN_pair> DNQ_new;
            while (!DNQ.empty()) {
                auto dnp = DNQ.top();
                auto n = dnp.second;
                DNQ.pop();
                int component = find_component(g, n, front_components);
                if (component != -1) {
                    separator.erase(n);
                    front_components[component].insert(n);
                    did_work = true;
                } else DNQ_new.push(dnp);
            }
            swap(DNQ_new, DNQ);
        } while (did_work);
    }


    void optimize_separator(const AMGraph3D &g, NodeSetUnordered &separator,
                            vector<NodeSetUnordered> &front_components) {
        if (separator.size() > 0) {
            NodeID n0 = *begin(separator);
            auto nbors = neighbors(g, separator);
            separator.insert(begin(nbors), end(nbors));
            front_components = connected_components(g, neighbors(g, separator));

            BreadthFirstSearch bfs(g);
            for (auto n: g.node_ids())
                bfs.mask[n] = 0;
            for (auto n: separator)
                bfs.mask[n] = 1;

            bfs.add_init_node(n0);
            while (bfs.Dijkstra_step());

            node_set_thinning(g, separator, front_components, bfs.dist);
        }
    }

    double separator_quality(const AMGraph3D& g, const NodeSetUnordered& s){
        uint min = -1;
        uint max = 0;
        for (const auto &d: front_components(g,s)) {
            auto temp = d.size();
            if (temp < min) min = temp;
            if (temp > max) max = temp;
        }
        return (double) min / max;
    }

    void thicken_separator(const AMGraph3D& g, NodeSetUnordered& sigma){
        auto C_F = front_components(g, sigma);
        for(const auto& c: C_F){
            NodeSetUnordered sigma_thick = sigma;
            for(auto e: c) sigma_thick.insert(e);
            if(front_components(g,sigma_thick).size() == 2) std::swap(sigma,sigma_thick);
        }
    }

    SepVec adjacent_separators(const AMGraph3D& g, const NodeSetUnordered& sigma){
        auto fc = front_components(g,sigma);
        SepVec res;
        vector<NodeSetUnordered> nsv(fc.size());
        for(auto s: sigma){
            for(auto n: g.neighbors(s)){
                for(uint c=0; c<fc.size(); ++c) if(fc[c].count(n)) nsv[c].insert(s);
            }
        }
        for(auto& c: nsv){
            res.push_back({separator_quality(g,c),c});
        }
        return res;
    }

    Separator shrink_separator(const AMGraph3D &g,
                          NodeSetUnordered &separator,
                          const Vec3d &sphere_centre, int opt_steps) {
        auto fc = front_components(g,separator);

        // Next, we thin out the separator until it becomes minimal (i.e. removing one more node
        // would make it cease to be a separator. We remove nodes iteratively and always remove the
        // last visited nodes first.

        auto smpos = g.pos;
        AttribVec<NodeID, double> center_dist;

        for (auto n: separator)
            center_dist[n] = sqr_length(smpos[n] - sphere_centre);
        smooth_attribute(g, smpos, separator, sqrt(separator.size()));


        node_set_thinning(g, separator, fc, center_dist);


        for (int iter = 0; iter < opt_steps; ++iter)
            optimize_separator(g, separator, fc);

        return {separator_quality(g,separator),separator};
    }

    NodeSetVec sepvec_to_nsv(const std::vector<Separator>& v){
        NodeSetVec res;
        res.reserve(v.size());
        for(const auto& sep:v){
            res.push_back({sep.quality,order(sep.sigma)});
        }
        return res;
    }

    using hrc = chrono::high_resolution_clock;

    /** For a given graph, g,  and a given node n0, we compute a local separator.
     The algorithm proceeds in a way similar to Dijkstra, finding a set of nodes separator such that there is anoter set of nodes, front,
     connected to separator via edges and front consists of two connected components.
     thick_front indicates whether we want to add a layer of nodes to the front before checking the number of connected  components.
     persistence is how many iterations the front must have two connected components before we consider the interior
     a local separator.
     The final node set returned is then thinned to the minimal separator.
     */
    Separator local_separator(const AMGraph3D &g, NodeID n0, double quality_noise_level, int optimization_steps,
                              uint growth_threshold, const Vec3d* static_centre) {

        // Create dynamic connectivity structure
        DynCon<NodeID, DYNCON> con = DynCon<NodeID,DYNCON>();
        // Create the separator node set and the temporary node set (used during computation)
        // The tmp sets are needed because of persistence. Whenever we have had two connected components
        // in front for a number of iterations = persistence, we go back to the original separator.
        NodeSetUnordered Sigma({n0});

        // Create the front node set. Note that a leaf node is a separator by definition,
        // so if there is only one neighbor, we are done here.
        auto N = g.neighbors(n0);
        if (N.size() == 0)
            return {0.0, NodeSetUnordered ()};
        if (N.size() == 1)
            return {0.0, NodeSetUnordered({n0}), 0, -1, 1};
        NodeSetUnordered F(begin(N), end(N));

        // Connect in dynamic connectivity structure
        for (auto v: F) {
            con.insert(v);
            for (auto w: g.neighbors(v)) {
                if (F.count(w) != 0) {
                    con.insert(v, w);
                }
            }
        }

        // We will need node sets for the connected components of the front.
        vector<NodeSetUnordered> C_F;

        // Create the initial sphere which is of radius zero centered at the input node.
        Vec3d centre = g.pos[n0];
        double radius = 0.0;
        NodeID last_n = AMGraph3D::InvalidNodeID; // Very last node added to separator.
        // Now, proceed by expanding a sphere
        while (con.front_size_ratio() < quality_noise_level) {
            if (growth_threshold != -1 && Sigma.size() >= growth_threshold) return {0.0, NodeSetUnordered()};

            // Find the node in front closest to the center
            const NodeID n = *min_element(begin(F), end(F), [&](NodeID a, NodeID b) {
                return sqr_length(g.pos[a] - centre) < sqr_length(g.pos[b] - centre);
            });

            // Update the sphere centre and radius to contain the new point.
            if(static_centre != nullptr) {
                const Vec3d p_n = g.pos[n];
                double l = length(centre - p_n);
                if (l > radius) {
                    radius = 0.5 * (radius + l);
                    centre = p_n + radius * (centre - p_n) / (1e-30 + length(centre - p_n));
                }
            }

            // Now, remove n from F and put it in Sigma.
            // Add n's neighbours (not in Sigma) to F.
            last_n = n;
            F.erase(n);
            Sigma.insert(n);
            // Add new edges in front to dynamic connectivity structure
            for (auto m: g.neighbors(n)) {
                if (Sigma.count(m) != 0 || F.count(m) != 0) continue;
                F.insert(m);
                con.insert(m);
                for (auto w: g.neighbors(m)) {
                    if (F.count(w) == 0) continue;
                    con.insert(m,w);
                }
            }
            // Remove edges connecting n to front
            con.remove(n,g.neighbors(n));

            // If the front is empty, we must have included an entire
            // connected component in "separator". Bail!
            if (F.size() == 0)
                return {0.0, NodeSetUnordered()};
        }
;
        return shrink_separator(g, Sigma, centre, optimization_steps);
    }

    NodeSetVec local_separators(AMGraph3D &g, SamplingType sampling, double quality_noise_level, int optimization_steps,
                                uint advanced_sampling_threshold) {

        // Because we are greedy: all cores belong to this task!
        const int CORES = thread::hardware_concurrency();

        // touched will help us keep track of how many separators use a given node.
        Util::AttribVec<NodeID, int> touched(g.no_nodes(), 0);

        vector<NodeID> node_id_vec;

        if (sampling == SamplingType::Advanced) {
            node_id_vec = multi_scale_vertex_sampling(g, quality_noise_level, optimization_steps,
                                                      advanced_sampling_threshold);
        } else if (sampling == SamplingType::Basic) {
            // Create a random order vector of nodes.
            for (auto n: g.node_ids())
                node_id_vec.push_back(n);
            srand(1);
            shuffle(begin(node_id_vec), end(node_id_vec), default_random_engine(rand()));
        } else {
            for (auto n: g.node_ids())
                node_id_vec.push_back(n);
        }

        auto t1 = hrc::now();

        // Each core will have its own vector of NodeSets in which to store
        // separators.
        vector<NodeSetVec> nsvv(CORES);
        int cnt = 0;
        auto create_separators = [&](int core) {
            auto &nsv = nsvv[core];
            for (auto n: node_id_vec) {
                double probability = 1.0 / int_pow(2.0, touched[n]);
                if (n % CORES == core && (sampling != SamplingType::Basic || rand() <= probability * RAND_MAX)) {
                    cnt += 1;
                    auto sep = local_separator(g, n, quality_noise_level, optimization_steps,-1);
                    // Store in pair to conserve compatibility.
                    std::pair<double, NodeSet> ns(sep.quality, order(sep.sigma));
                    if (ns.second.size() > 0) {
                        nsv.push_back(ns);
                        for (auto m: ns.second)
                            touched[m] += 1;
                    }
                }
            }
        };

        vector<thread> threads(CORES);
        for (int i = 0; i < CORES; ++i)
            threads[i] = thread(create_separators, i);

        for (int i = 0; i < CORES; ++i)
            threads[i].join();

        auto t2 = hrc::now();

        NodeSetVec node_set_vec_global;
        for (const auto &nsv: nsvv)
            for (const auto &ns: nsv)
                node_set_vec_global.push_back(ns);

        auto sep_bef = node_set_vec_global.size();
        greedy_weighted_packing(g, node_set_vec_global, true);
        auto sep_aft = node_set_vec_global.size();
        auto t3 = hrc::now();

        cout << "Computed " << cnt << " separators" << endl;
        cout << "Found " << sep_bef << " separators" << endl;
        cout << "Packed " << sep_aft << " separators" << endl;
        cout << "Finding separators: " << (t2 - t1).count() * 1e-9 << endl;
        cout << "Packing separators: " << (t3 - t2).count() * 1e-9 << endl;

        // Color the node sets selected by packing, so we can get a sense of the
        // selection.
        color_graph_node_sets(g, node_set_vec_global);

        return node_set_vec_global;
    }

    NodeSetVec multiscale_local_separators(AMGraph3D &g, SamplingType sampling,const uint grow_threshold,double quality_noise_level, int optimization_steps) {
        // Because we are greedy: all cores belong to this task!
        //const unsigned int CORES = std::min(8u,thread::hardware_concurrency());

        const int CORES = thread::hardware_concurrency();
        const int CORES_SEC = std::min(CORES,2);

        Util::AttribVec<NodeID, uint> touched(g.no_nodes(), 0);

        size_t count_computed = 0;
        size_t count_found = 0;
        size_t count_packed = 0;

        long time_creating_separators = 0, time_shrinking = 0, time_expanding = 0, time_packing = 0, time_filtering = 0;
        auto timer = hrc::now();

        vector<thread> threads(CORES);

        // Each core will have its own vector of Separators in which to store
        // separators.
        vector<vector<Separator> > separator_vv(CORES);
        auto create_separators = [&](const int core, const AMGraph3D &g, const int level) {
            auto &separator_v = separator_vv[core];
            const size_t chunk_size = (g.no_nodes()+CORES-1)/CORES;
            for (size_t i=core*chunk_size; i<(core+1)*chunk_size && i<g.no_nodes(); ++i) {
                double probability = 1.0 / int_pow(2.0, touched[i]);
                if (sampling==SamplingType::None || rand() <= probability * RAND_MAX) {
                    ++count_computed;
                    auto separator = local_separator(g, i, quality_noise_level, optimization_steps,
                                                                grow_threshold);
                    if (separator.sigma.size() > 0) {
                        SepVec adjsep = MULTI_SHRINK ? adjacent_separators(g,separator.sigma) : SepVec();
                        uint c = 0;
                        do{
                            separator.id = count_found;
                            separator.grouping = count_found;
                            ++count_found;
                            separator_v.push_back(separator);
                            if (sampling!=SamplingType::None) {
                                for (auto m: separator.sigma) {
                                    touched[m]++;
                                }
                            }
                            if(c < adjsep.size()) separator = adjsep[c++];
                        } while(c<adjsep.size());
                    }
                }
            }
        };

        auto shrink_expand = [&](
                int core,
                const vector<Separator> &node_set_vec_global,
                const AMGraph3D &g_current,
                const AMGraph3D &g_next,
                const vector<vector<NodeID>> &exp_map_current,
                const int level) {
            auto &current_level_separator_vec = separator_vv[core];
            const size_t chunk_size = (node_set_vec_global.size()+CORES_SEC-1)/CORES_SEC;
            for (unsigned int i = core*chunk_size; i < (core+1)*chunk_size && i < node_set_vec_global.size(); i++) {
                const auto &sep = node_set_vec_global[i];
                auto local_timer = hrc::now();

                // Do not include if separator is a leaf. Leaves in the input graph is still included since we do not expand on that level.
                if (sep.sigma.size() == 1 && g_current.neighbors(*sep.sigma.begin()).size() == 1) {
                    continue;
                }

                uint old_size = sep.sigma.size();

                // Expand.

                NodeSetUnordered Sigma;
                for (NodeID old_v: sep.sigma) {
                    for (NodeID new_v: exp_map_current[old_v]) Sigma.insert(new_v);
                }

                for(uint j=0;j<THICC_SEP;j++) thicken_separator(g_next,Sigma);

                //time_expanding += (hrc::now() - local_timer).count(); // TODO: This might be a race condition.
                //local_timer = hrc::now();

                // Shrink.

                Vec3d centre = approximate_bounding_sphere(g_next, Sigma).first;

                Separator trimmed_sep;

                trimmed_sep = shrink_separator(g_next, Sigma, centre, optimization_steps);
                trimmed_sep.grouping = sep.grouping;
                current_level_separator_vec.push_back(trimmed_sep);
                if(sampling==SamplingType::Advanced){
                    for(auto n: trimmed_sep.sigma) touched[n]++;
                }

                time_shrinking += (hrc::now() - local_timer).count(); //TODO: Also race condition.
            }
        };

        auto t1 = hrc::now();

        auto msg = Geometry::multiscale_graph(g, grow_threshold, true);

        auto t2 = hrc::now();

        //std::cout<<"MSG created: "<<msg.layers.size()<<" levels total"<<std::endl;

        vector<Separator> separator_vector_global;

        for (int level = msg.layers.size() - 1; level >= 0; --level) {
            timer = hrc::now();
            const auto &g_current = msg.layers[level];
            const auto &exp_map_current = msg.expansion_map_vec[level];

            //std::cout << "Finding separators on lvl "<<level<<std::endl;

            // Determine separators
            for (int i = 0; i < CORES; ++i)
                threads[i] = thread(create_separators, i, g_current,level);

            for (auto& t: threads) t.join();

            //std::cout << "Separators found"<<std::endl;

            for (auto &separator_v: separator_vv)
                for (auto &sep: separator_v) {
                    separator_vector_global.push_back(sep);
                }

            for (auto &nsv: separator_vv) {
                nsv.clear();
            }
            time_creating_separators += (hrc::now() - timer).count();

            // Should do nothing on first layer.
            //size_t temp = node_set_vec_global.size();
            timer = hrc::now();
            separator_vector_global = filter_duplicate_separators(separator_vector_global);
            time_filtering += (hrc::now() - timer).count();
            //cout << "Filtered: " <<  temp - node_set_vec_global.size() << endl;

            // Pack
            timer = hrc::now();
            capacity_packing(g_current, separator_vector_global, true, msg.capacity_vec_vec[level]);
            time_packing += (hrc::now() - timer).count();

            // Cleanup touched
            for (uint i = 0; i < touched.size(); ++i) {
                touched[i] = 0;
            }

            // Save graph
            //graph_save("msg"+ to_string(level)+".graph",g_current);
            //std::cout << "Saving msg"<<level<<".graph"<<std::endl;

            // Expand and shrink.
            if (level != 0) { // Nothing to expand to on final level.
                //touched = (g.no_nodes(),0);

                timer = hrc::now();
                for (int i = 0; i < CORES_SEC; ++i)
                    threads[i] = thread(shrink_expand, i, separator_vector_global, g_current, msg.layers[level - 1],
                                        exp_map_current,level);

                for (int i = 0; i < CORES_SEC; ++i){
                    threads[i].join();
                }

                time_expanding += (hrc::now() - timer).count();
                separator_vector_global.clear();
                for (const auto &sep_v: separator_vv)
                    for (const auto &sep: sep_v) {
                        separator_vector_global.push_back(sep);
                    }

                for (auto &nsv: separator_vv) {
                    nsv.clear();
                }
            }
        }

        count_packed = separator_vector_global.size();

        auto t3 = hrc::now();

        cout << "#####################" << endl;
        cout << "Computed " << count_computed << " separators" << endl;
        cout << "Found " << count_found << " separators" << endl;
        cout << "Packed " << count_packed << " separators" << endl;
        cout << "#####################" << endl;
        cout << "Building multilayer graph: " << (t2 - t1).count() * 1e-9 << endl;
        //cout << "Creating separators: " << (t3 - t2).count() * 1e-9 << endl;
        //cout << "#####################" << endl;
        cout << "Searching for restricted separators: " << time_creating_separators * 1e-9 << endl;
        cout << "Packing separators: " << time_packing * 1e-9 << endl;
        cout << "Expanding separators: " << time_expanding * 1e-9 << endl;
        cout << "Shrinking separators: " << time_shrinking * 1e-9 << endl;
        cout << "Filtering separators: " << time_filtering * 1e-9 << endl;
        cout << "#####################" << endl;

        // Color the node sets selected by packing, so we can get a sense of the
        // selection.
        NodeSetVec node_set_color_vec;
        for (const auto &sep: separator_vector_global) {
            node_set_color_vec.push_back(make_pair(sep.quality, order(sep.sigma)));
        }

        color_graph_node_sets(g, node_set_color_vec);

        return sepvec_to_nsv(separator_vector_global);
    }

    MultiScaleGraph multiscale_graph(const AMGraph3D &g, const uint threshold, bool recursive) {
        MultiScaleGraph msg;

        msg.layers = std::vector<AMGraph3D>();
        msg.expansion_map_vec = std::vector<ExpansionMap>();
        msg.capacity_vec_vec = CapacityVecVec();

        AMGraph3D graph_current;
        size_t vertex_target;
        size_t vertex_count;


        auto graph_decimate = [&](const AMGraph3D& g, size_t to_remove)->AMGraph3D {
            AMGraph3D g_temp = g;
            auto map_temp = vector<vector<NodeID>>(g.no_nodes());

            Util::AttribVec<NodeID, int> touched(g.no_nodes(),0);
            priority_queue<SkeletonPQElem> Q;

            int total_work = 0;
            bool did_work = true;

            while(total_work < to_remove && did_work){
                did_work = false;
                touched.clear();
                for (auto n0: g_temp.node_ids()) {
                    for (auto n1: g_temp.neighbors(n0)) {
                        if(n1>n0) continue; // Only visit edge a,b a<b and not b,a
                        double pri;
                        pri = -g.sqr_dist(n0, n1);
                        Q.push(SkeletonPQElem(pri, n0, n1));
                    }
                }
                //cout << "Q was empty now has "<<Q.size()<<endl;

                //cout << "Looping tw: "<<total_work<<", tr: "<<to_remove<<", Q: "<<Q.size()<<endl;
                while(!Q.empty()){
                    auto skel_rec = Q.top();
                    Q.pop();
                    if(touched[skel_rec.n0] == 0 && touched[skel_rec.n1] == 0) { // Merge vertices
                        auto e = g_temp.find_edge(skel_rec.n0, skel_rec.n1);
                        if(e != AMGraph::InvalidEdgeID){
                            g_temp.merge_nodes(skel_rec.n0, skel_rec.n1);
                            // Merging removes n0 from graph
                            map_temp[skel_rec.n1].push_back(skel_rec.n0);
                            for(auto i: map_temp[skel_rec.n0]){
                                map_temp[skel_rec.n1].push_back(i);
                            }
                            touched[skel_rec.n0] = touched[skel_rec.n1] = 1;
                            ++total_work;
                            did_work = true;
                        }
                    }
                }
            }

            //cout << "Finished decimate tw: "<<total_work<<", tr: "<<to_remove<<", dw: "<<did_work<<endl;
            auto map_result = vector<vector<NodeID>>(g.no_nodes() - total_work);
            auto cap_result = vector<size_t>(g.no_nodes() - total_work, 0);

            // Perform a special case cleanup that maintains expansion map
            AMGraph3D g_result; // New graph
            map<NodeID,NodeID> node_map;
            size_t node_new_index = 0;

            // For all nodes that are not too close to previously visited nodes
            // create a new node in the new graph
            for(auto n: g_temp.node_ids()){
                if (std::isnan(g_temp.pos[n][0])) {
                    node_map[n] = AMGraph::InvalidNodeID;
                } else {
                    node_map[n] = g_result.add_node(g_temp.pos[n]);
                    g_result.node_color[node_map[n]] = g_temp.node_color[n];
                    for (auto i : map_temp[n]) {
                        map_result[node_new_index].push_back(i);
                        cap_result[node_new_index] += msg.capacity_vec_vec.back()[i];
                    }
                    // Also add the node itself.
                    map_result[node_new_index].push_back(n);
                    cap_result[node_new_index] += msg.capacity_vec_vec.back()[n];
                    ++node_new_index;
                }
            }

            // For all edges in old graph, create a new edge
            for (auto n: g_temp.node_ids())
                if (node_map[n] != AMGraph::InvalidNodeID)
                    for (AMGraph::NodeID &nn: g_temp.neighbors(n)) {
                        AMGraph::EdgeID e = g_result.connect_nodes(node_map[n], node_map[nn]);
                        if (g_result.valid_edge_id(e)) {
                            AMGraph::EdgeID e_old = g_temp.find_edge(n, nn);
                            if (g_temp.valid_edge_id(e_old))
                                g_result.edge_color[e] = g_temp.edge_color[e_old];
                            else
                                g_result.edge_color[e] = Vec3f(0);
                        }
                    }

            msg.capacity_vec_vec.push_back(cap_result);
            msg.expansion_map_vec.push_back(map_result);
            return g_result;
        };

        graph_current = g;

        // The first layer is always the input graph.
        msg.layers.push_back(graph_current);
        msg.expansion_map_vec.emplace_back(graph_current.no_nodes());
        msg.capacity_vec_vec.emplace_back(graph_current.no_nodes());
        for (uint i = 0; i < graph_current.no_nodes(); ++i) {
            msg.expansion_map_vec[0][i] = std::vector<NodeID>(1, i);
            msg.capacity_vec_vec[0][i] = 1;
        }

        vertex_target = g.no_nodes();

        while (vertex_target > threshold) {
            vertex_count = graph_current.no_nodes();
            vertex_target = vertex_count/2;
            graph_current = graph_decimate(graph_current,graph_current.no_nodes()-vertex_target);
            if (vertex_count == graph_current.no_nodes()){
                //cout << "Early return no edges to remove" <<endl;
                //cout << "Wanted to remove "<<edges_to_remove<<" from graph with "<<vertex_count<<" vertices but failed"<<endl;
                break; // Was unable to remove any edges.
            }

            msg.layers.push_back(graph_current);


        }

        return msg;
    }

    unsigned long thinness_measure(const AMGraph3D &g, uint samples, double quality_noise_level, int optimization_steps) {
        // Grow separators to determine the median thinness of the model
        // Because we are greedy: all cores belong to this task!
        const int CORES = thread::hardware_concurrency();

        // Create a random order vector of nodes.
        vector<NodeID> node_id_vec;
        for (auto n: g.node_ids())
            node_id_vec.push_back(n);
        srand(1);
        shuffle(begin(node_id_vec), end(node_id_vec), default_random_engine(rand()));

        vector<NodeID> sampled_vertices_vec;
        for (uint i = 0; i < samples && i < node_id_vec.size(); ++i) {
            sampled_vertices_vec.push_back(node_id_vec[i]);
        }

        vector<Separator> separator_vec;
        // From each sampled vertex, grow a separators.
        for (auto n: sampled_vertices_vec) {
            // TODO: Make parallel.
            const auto &sep = local_separator(g, n, quality_noise_level, optimization_steps, -1);
            separator_vec.push_back(sep);
        }

        // Sort separators according to growth_measure and pick median.
        auto separator_greater = [](const Separator &a, const Separator &b) {
            return (a.growth_measure < b.growth_measure);
        };
        sort(separator_vec.begin(), separator_vec.end(), separator_greater);
        auto median_growth_measure = separator_vec[separator_vec.size() / 2].growth_measure;

        return median_growth_measure;
    }

// --------- Edits Helen --------

double angle_z_axis(Geometry::AMGraph3D& g, NodeID one, NodeID two){
    //n = bottom node (one), nb = edge node (two), c = +1 z direction node
    
    auto xn = g.pos[one][0];
    auto xnb = g.pos[two][0];
    auto xc = xn;
    auto yn = g.pos[one][1];
    auto ynb = g.pos[two][1];
    auto yc = yn;
    auto zn = g.pos[one][2];
    auto znb = g.pos[two][2];
    auto zc = zn + 0.5;


    // edge direction
    auto xb = xnb-xn;
    auto yb = ynb-yn;
    auto zb = znb-zn;

    //z direction direction
    auto xcd = xc-xn;
    auto ycd = yc-yn;
    auto zcd = zc-zn;

    auto length_b = sqrt(xb*xb + yb*yb + zb*zb);
    auto length_c = sqrt(xcd*xcd + ycd*ycd + zcd*zcd);

//    cout << "length b and c: " << length_b << " " << length_c <<  endl;

    auto dot_p = ((xb/length_b)*(xcd/length_c) + (yb/length_b)*(xcd/length_c) + (zb/length_b)*(zcd/length_c));

    auto length_b_unit = sqrt((xb/length_b)*(xb/length_b) + (yb/length_b)*(yb/length_b) + (zb/length_b)*(zb/length_b));
    auto length_c_unit = sqrt((xcd/length_c)*(xcd/length_c) + (ycd/length_c)*(ycd/length_c) + (zcd/length_c)*(zcd/length_c));
    
    auto angle = (acos(dot_p/(length_b_unit*length_c_unit))*180)/3.141592;
    
    return angle;
    
}


AMGraph3D bottom_node(Geometry::AMGraph3D& g){
    
    //Fnding z-values and the lowest edges
    
    vector<double> z_values;
    vector<double> z_values_low;
    vector<NodeID> z_values_low_index;
    vector<double> ave_radius;

    //Loading z-coordinates into vector
    for(auto i: g.node_ids()){
        z_values.push_back(g.pos[i][2]);
       // cout << g.pos[i][2] << " ";
     }
    //cout << "Stop" << endl;
      
    //Sort the z values and find the X lowest nodes
    int X = 30;
    for(int i = 0; i < X; i++){
        double min = 1000;
        NodeID index;
        for(int j = 0; j < z_values.size(); j++){
            if(z_values[j] < min){
                min = z_values[j];
                index = j;
            }
        }
        z_values_low.push_back(min);
        z_values_low_index.push_back(index);
        z_values[index] += 10;
        g.node_color[index] = Vec3f(1, 0, 0);
    }
    
    int I = 0;
    NodeID root;
    for(int i = 0; i < z_values_low.size(); i++){
        double angle = 1000;
        auto NB = g.neighbors(z_values_low_index[i]);
        for(auto j: NB){
            if(g.pos[j][2] > z_values_low[i]){ //If the NB is a higher z value, find angle of edge relative to z-axis
                angle = angle_z_axis(g, z_values_low_index[i], j);
                
                g.node_color[z_values_low_index[i]] = Vec3f(0, 0, 1);
                
                if(angle < 45){
                    I += 1;
                    
                    g.node_color[z_values_low_index[i]] = Vec3f(0, 1, 0); //Color the bottom node of the "vertical edge green"
                    
                    root = z_values_low_index[i];
                    
                    cout << "Found root-node " << z_values_low_index[i] << endl;
                    
                }
            }
        }
        
        //Set limit for how many edge should be found
        if(I > 0){
            break;
        }
    }

    vector<NodeID> remove;
    for(int i = 0; i < z_values_low_index.size(); i++){
        if(g.pos[z_values_low_index[i]][2] < g.pos[root][2]){
            g.remove_node(z_values_low_index[i]);
        }
    }
    
    
    return g;
}


NodeID bottom_node_return(Geometry::AMGraph3D& g){
    
    //Fnding z-values and the lowest edges
    
    vector<double> z_values;
    vector<double> z_values_low;
    vector<NodeID> z_values_low_index;

    //Loading z-coordinates into vector
    for(auto i: g.node_ids()){
        z_values.push_back(g.pos[i][2]);
        cout << g.pos[i][2] << " ";
     }
    cout << "Stop" << endl;
      
    //Sort the z values and find the X lowest nodes
    int X = 30;
    for(int i = 0; i < X; i++){
        double min = 1000;
        NodeID index;
        for(int j = 0; j < z_values.size(); j++){
            if(z_values[j] < min){
                min = z_values[j];
                index = j;
            }
        }
        z_values_low.push_back(min);
        z_values_low_index.push_back(index);
        z_values[index] += 10;
        g.node_color[index] = Vec3f(1, 0, 0);
    }
    
    int I = 0;
    NodeID root_node;
    for(int i = 0; i < z_values_low.size(); i++){
        double angle = 1000;
        auto NB = g.neighbors(z_values_low_index[i]);
        for(auto j: NB){
            if(g.pos[j][2] > z_values_low[i]){ //If the NB is a higher z value, find angle of edge relative to z-axis
                angle = angle_z_axis(g, z_values_low_index[i], j);
                
                
                if(angle < 45){
                    I += 1;
                    
                    g.node_color[z_values_low_index[i]] = Vec3f(0, 1, 0); //Color the bottom node of the "vertical edge green"
                    
                    root_node = z_values_low_index[i];
                }
            }
        }
        
        //Set limit for how many edge should be found
        if(I > 0){
            break;
        }
    }
    
    
    vector<NodeID> remove;
    for(int i = 0; i < z_values_low_index.size(); i++){
        if(g.pos[z_values_low_index[i]][2] < g.pos[root_node][2]){
            g.remove_node(z_values_low_index[i]);
        }
    }

    cout << "root_node: " << root_node << endl;
    
    
    
    return root_node;
}


//Find distances to all nodes
pair<AttribVec<NodeID, int>,AttribVec<NodeID, NodeID>> distance_to_all_nodes(Geometry::AMGraph3D& g){
    
//        NodeID s = skel_root_node(g);  //for branch 22
        NodeID s = bottom_node_return(g); // for normal
        NodeID next;
        int walking = 0;
        NodeID crossings = s; // should be equal to S, which is the starting vertex
          
        Util::AttribVec<NodeID, int> dist(g.no_nodes(),0);
        Util::AttribVec<NodeID, NodeID> pred(g.no_nodes(),0);
        Util::AttribVec<NodeID, NodeID> prev_crossing(g.no_nodes(),0);
        Util::AttribVec<NodeID, int> cross_dist(g.no_nodes(),0);
        
        queue<NodeID> Q;
        forward_list<NodeID> cross_node_Q{};
         
        dist[crossings] = 0; //dist to start vertex is 0
        Q.push(crossings); // start vertex
        
        
        while(!Q.empty()){
            auto u = Q.front();
            Q.pop();
            auto no_NB = g.neighbors(u).size();
//            cout << no_NB << " no of NB" << endl;
            
    //        g.node_color[u] = Vec3f(1,0,0);

//            straight branch
//            if(u  == s && dist[u] == 0){

//
//                cout <<"found start vertex " << endl;
//                NodeID t;
//                for(auto w: g.neighbors(u)){ t = w; }
//                Q.push(t);
//                cross_node_Q.push_front(u);
//                next = t;
//                dist[u] = 1;
//                pred[next] = u;
//                walking += 1;
//
//            }
            
            if(no_NB == 2){
                 int check = 0;
                for(auto t: g.neighbors(u)){ //go in the  right direction, the one notvisited before
                    if(dist[t] == 0){
//                        cout << "At a straight edge part " << endl;
                        Q.push(t);
                        next = t;
                    }
                    else if(dist[t] != 0){
                        check += 1;
                    }

                }
                dist[u] = dist[pred[u]] + 1;
                pred[next] = u;
                walking += 1;
                if(check == no_NB){
                    auto q = cross_node_Q.front();
                    cross_node_Q.pop_front();
                    cross_dist[q] += walking;
                    Q.push(q);
                    walking = 0;
//                    cout << "Hopping, found no avaliable paths in straight branch" << endl;
                }

            }
            
            //at a crossing
            else if(no_NB > 2){
//                cout << "At a crossing " << endl;
                int check = 0;
                for(auto t: g.neighbors(u)){ //go in a direction in the crossing we havent been before
                    if(dist[t] == 0){
//                        cout << "Going in a direction from the crossing " << endl;
                        cross_node_Q.push_front(u);
                        Q.push(t);
                        pred[t] = u;
                        dist[u] = dist[pred[u]] + 1;
                        prev_crossing[u] = crossings;
                        cross_dist[u] += walking;
                        walking = 0;
                        crossings = u;
                        break;
                    }
                    //If we are at a crossing where all branches have been meet
                    else if(dist[t] != 0){
                        check += 1;
                        if(check == no_NB){
                            if(cross_node_Q.empty()){ //if we have visited the whole tree then stop
                                break;
                            }
//                            cout << "last root we see " << u << endl;
                            auto q = cross_node_Q.front();
                            cross_node_Q.pop_front();
                            cross_dist[q] += cross_dist[u];
                            Q.push(q);
//                            cout << "hopping back" << endl;
                        }

                    }
                }
            }

            //at branch ends or the start vertex
            else if (no_NB == 1){
                // If the vertex is the start vertex S
                //go in the  right direction, the one not visited before
                if(u == s ){ //should be start vertex S
//                    cout <<"found start vertex " << endl;
                    NodeID t;
                    for(auto w: g.neighbors(u)){ t = w; }
                    Q.push(t);
                    next = t;
                    dist[u] = 1;
                    pred[next] = u;
                    walking += 1;
                }
                else if(1 == 1){
                    // if the vertex is a end of a branch
//                    cout << "at the end of a branch " << endl;
                    dist[u] = dist[pred[u]] + 1;
                    
                    auto q = cross_node_Q.front();
                    cross_node_Q.pop_front();
                    cross_dist[q] += walking;
                    Q.push(q);
                    walking = 0;
                }
                
         
                
            }
        }
    return make_pair(dist,pred);
}

AMGraph3D attach_branches(Geometry::AMGraph3D& g,  double connect_dist, double angle_straight, double angle_complex){
    
    auto a_pair = distance_to_all_nodes(g); //Function finding all distances
    auto dist = a_pair.first;

    //:------------------------------------------------------------:

    //Create a tree, so we can use m_closest to  estimate distances and connect lose branches
    KDTree<Vec3d, AMGraph3D::NodeID> tree_skeleton;
    KDTree<Vec3d, AMGraph3D::NodeID> tree_branches;

    vector<NodeID> loose;
    Util::AttribVec<NodeID, int> loose_seen(g.no_nodes(),0);  //part of the big skeleton, 0 loose branch, 1 has ben searched
    
    //Color all nodes that can not be reached red
    NodeID lose_nodes = 0;
    NodeID connected_nodes = 0;
    for(auto i = 0; i < g.no_nodes(); i++ ) {
        if(dist[i] == 0){
            g.node_color[i] = Vec3f(1,0,0);
            lose_nodes += 1;
    
            //Create a vector with these LOOSE nodes
            loose.push_back(i);
            tree_branches.insert(g.pos[i], i);
        }
        else{
            connected_nodes += 1;
            tree_skeleton.insert(g.pos[i], i);
           }
    }
    
    tree_skeleton.build();
    tree_branches.build();
    
    
    //vector<int> single_branches;
    queue<NodeID> q; //the queue
    queue<NodeID> branch; //the current branch
    
    //Distance statistics
    int no_connections = 0;
    double ave_dist_total = 0;
    vector<double> median_dist;
    
    
//    go through each  component WITH NO CROSSINGS -> the simple ones
    for(auto s: loose){
        //swap(branch, empty); //clear the queue
    
        //empty branch
        while(!branch.empty()){
            branch.pop();
        }
    
        //check if s seen before -> if yes, then break
        if(loose_seen[s] == 0){
            vector<NodeID> remember_branch;
            loose_seen[s] = 1;
    
            //make a queue
            q.push(s);
            branch.push(s);
    
            //If we see a crossing
            int NB_is_3 = 0;

            //while
            while(!q.empty()){
                //go through s's branch, start over if found a crossing
                //otherwise save the branch as we loop in a new queue, and color green when we end
                auto current = q.front();
                q.pop();
                auto NB = g.neighbors(current).size();
                loose_seen[current] = 1;
    
                branch.push(current);
                //Then pass on to the next neighbour and check again
                for(auto t: g.neighbors(current)){
                    if(loose_seen[t] == 0){ //if we havent seen the NB before, add to queue
                        q.push(t);
                    }
                }
    
                if(NB > 2){
                    NB_is_3 = 1;
                    }

                if(q.empty() ){ // ************ && NB_is_3 == 0
                    cout << "NEW BRANCH"  << endl;
                    //If the queue is empty (finished the branch), we color this branch
                        
                    vector<NodeID> critical_nodes; //Check these nodes in the branch for the closest NB
                    double branch_internal_angle = 1000;
                    double internal_angle = 0;
                    NodeID add_critical_node = 0;
                        
                    while(!branch.empty()){
                        NodeID node = branch.front();
                        branch.pop();
    
                        remember_branch.push_back(node);
 
                        //________________________
                        //Check the branch for critical changes in direction
                        vector<NodeID> neighbours; //NB for each  nodes
                        
                        auto NB_size = g.neighbors(node).size();
                        cout << "*************************************** The size of the NB  " << NB_size << endl;
                            
                        //If the node has NB=1 then just add to critical_nodes
                        if(NB_size == 1){
                            critical_nodes.push_back(node);
                        }
                            
                        //Find the node with NB=2 (if any) that has the smallest angle
                        //If this angle is considered small enough (the branchis  not  straight), then  add that to
                        //critical_nodes as well
                        if(NB_size > 1){
                                
                            //All crossings in the complex branches should be  consideres
                            if(NB_size > 2 && NB_is_3 == 1){
                                critical_nodes.push_back(node);
                            }
                                
                            //Add the  neightbours to a vector
                            for(auto j: g.neighbors(node)){
                                neighbours.push_back(j);
                            }
                                
                            cout << "__________________________ The size of the NB vector " << neighbours.size() << endl;
                                
                            //n = node, nb = node NB, c = connect node
                            auto xn = g.pos[node][0];
                            auto xnb = g.pos[neighbours[0]][0];
                            auto xc = g.pos[neighbours[1]][0];
                            auto yn = g.pos[node][1];
                            auto ynb = g.pos[neighbours[0]][1];
                            auto yc = g.pos[neighbours[1]][1];
                            auto zn = g.pos[node][2];
                            auto znb = g.pos[neighbours[0]][2];
                            auto zc = g.pos[neighbours[1]][2];

                            double xb = xnb-xn;
                            double yb = ynb-yn;
                            double zb = znb-zn;

                            // connect direction
                            double xcd = xc-xn;
                            double ycd = yc-yn;
                            double zcd = zc-zn;

                            double length_b = sqrt(xb*xb + yb*yb + zb*zb);
                            double length_c = sqrt(xcd*xcd + ycd*ycd + zcd*zcd);
                                           
                            double dot_p = ((xb/length_b)*(xcd/length_c) + (yb/length_b)*(xcd/length_c) + (zb/length_b)*(zcd/length_c));

                            double length_b_unit = sqrt((xb/length_b)*(xb/length_b) + (yb/length_b)*(yb/length_b) + (zb/length_b)*(zb/length_b));
                            double length_c_unit = sqrt((xcd/length_c)*(xcd/length_c) + (ycd/length_c)*(ycd/length_c) + (zcd/length_c)*(zcd/length_c));

                            internal_angle = (acos(dot_p/(length_b_unit*length_c_unit))*180)/3.141592;
                                
                            cout << "WE FOUND AN INTERNAL ANGLE_________________" << internal_angle << endl;
                                
                            //Find the smallest internal angle in the branch for STRAIGHT BRANCHES
                            if(internal_angle < branch_internal_angle && NB_is_3 == 0){
                                cout << "WE connect_ *****   _" << internal_angle << endl;
                                branch_internal_angle = internal_angle;
                                add_critical_node = node; //neighbours[1]
                                critical_nodes.push_back(add_critical_node); /// Just added as a test
                            }
                                
                            //Find the critical angles for COMPLEX BRANCHES
                            if(internal_angle < angle_complex && NB_is_3 == 1){
                                critical_nodes.push_back(node);
                                g.node_color[node] = Vec3f(0,1,0);
                            }
                        }
                           
                        //________________________
                    } //End while for going through the empty branch
                        
                    //If the angle is consideres a direction of change (angle < 140 deg) then we consider this node as well
                    if(branch_internal_angle < angle_straight && NB_is_3 == 0){
                        critical_nodes.push_back(add_critical_node);
                        g.node_color[add_critical_node] = Vec3f(0,1,0);
                    }
  

//                  _____________________________
//                  WE HAVE FOUND THE CRITICAL NODES ABOVE
//                  NOW WE WILL DECIDE WHICH ONE TO CONNECT TO
                    
                    NodeID closest_node = 0; //the node in the   branch that is choosen
                    NodeID connect_node = 0; //the node in the big skeleton we prefer
                    double min_dist = 10000;
                    double pred_dist = 10000;
                    double best_angle = 0; //0
                    double angle = 0;
                        
                    for(auto n: critical_nodes){ //g.neighbors(node).size() == 1
                        cout << "ONE NB node found"  << endl;
                        g.node_color[n] = Vec3f(0,1,0);
                        int N_closest = 5; //5
                        auto rad = 1;  //2

                        auto closests = tree_skeleton.m_closest(N_closest, g.pos[n], rad);
                        cout << "nbors size: " << closests.size() << endl;

                        //A loop, that find the closest point using sqrt  dist
                        //And the closest which also dont have loose_seen == 1

                       for(const auto& nn: closests){ //(const auto& nn: closests)
                           cout << "For the nn closest NBs: "  << endl;
                           g.node_color[nn.v] = Vec3f(0,0,1);

                           cout << "Distance for the NB: " << dist[nn.v] << endl;
                                                            
                                                            
                           if(nn.v != n){//loose_seen[nn.v] == 0 && nn.v != node
                               //calculate distance between node
                               auto sqr_dist = sqrt(g.sqr_dist(nn.v, n));

                               //NBs to the node
                               auto node_NB = g.neighbors(n);
                               for(auto j: node_NB){
                               //calculate the angle between the NB/node/connect_node
                               //Do this for either side of the node if NB size = 2

                               //n = node, nb = node NB, c = connect node
                               auto xn = g.pos[n][0];
                               auto xnb = g.pos[j][0];
                               auto xc = g.pos[nn.v][0];
                               auto yn = g.pos[n][1];
                               auto ynb = g.pos[j][1];
                               auto yc = g.pos[nn.v][1];
                               auto zn = g.pos[n][2];
                               auto znb = g.pos[j][2];
                               auto zc = g.pos[nn.v][2];


                          // branch direction
                               auto xb = xnb-xn;
                               auto yb = ynb-yn;
                               auto zb = znb-zn;

                          //connect direction
                               auto xcd = xc-xn;
                               auto ycd = yc-yn;
                               auto zcd = zc-zn;

                               auto length_b = sqrt(xb*xb + yb*yb + zb*zb);
                               auto length_c = sqrt(xcd*xcd + ycd*ycd + zcd*zcd);
                 
                               cout << "length b and c: " << length_b << " " << length_c <<  endl;

                               auto dot_p = ((xb/length_b)*(xcd/length_c) + (yb/length_b)*(xcd/length_c) + (zb/length_b)*(zcd/length_c));

                               auto length_b_unit = sqrt((xb/length_b)*(xb/length_b) + (yb/length_b)*(yb/length_b) + (zb/length_b)*(zb/length_b));
                               auto length_c_unit = sqrt((xcd/length_c)*(xcd/length_c) + (ycd/length_c)*(ycd/length_c) + (zcd/length_c)*(zcd/length_c));


                               angle = (acos(dot_p/(length_b_unit*length_c_unit))*180)/3.141592;

                               cout << "Angle: "  << angle << endl;

                               //For STRAIGHT  BRANCHES
                                   if((min_dist > length_c && angle > best_angle*1.1) && NB_is_3 == 0){  //((min_dist*2.5 > length_c && angle > best_angle*1.1) && NB_is_3 == 0)
                                   // min_dist*2.5 > length_c && angle > best_angle*1.1) && NB_is_3 == 0     error 36.8283
                                    // min_dist*1.5 > length_c && angle > best_angle*1.1) && NB_is_3 == 0    error 36.8511
                                    //angle > best_angle) && NB_is_3 == 0      error 38.8442
                                       // (angle > best_angle) && NB_is_3 == 0    error 36.8344   rad = 0.5  N=3
                                    cout << "We choose to change to connect this new node "  << endl;
                                    closest_node = nn.v;
                                    min_dist = length_c; //length_c
                                    connect_node = n; // n is the currently invested node from the vector of critical nodes
                                    best_angle = angle;
                               }
                                                                    
                               //For COMPLEX BRANCHES
                                   if(dist[nn.v] < (pred_dist+8)  && NB_is_3 == 1){  //dist[nn.v] < pred_dist*1.3 && NB_is_3 == 1
                                    if((min_dist > length_c)){ // (min_dist*2.5 > length_c && angle > best_angle)
                                        cout << "We choose to change to connect this new node "  << endl;
                                        closest_node = nn.v;
                                        min_dist = length_c; //length_c
                                        connect_node = n;
                                        best_angle = angle;
                                        pred_dist = dist[nn.v];
                                     }
                                }
                           }
                       }
                  }
             }

                        //Connect the found nodes
                        if(closest_node != 0 && connect_node != 0){
                            int connected = 0;
                            
                            cout << "________________________________"  << endl;
                            cout <<"WE CONNECTS" << endl;
                            cout <<"min dist " << min_dist << endl;
                            cout << "The angle: " << best_angle << endl;
                            if(connect_dist == 0){ //Connect all if no restrains are given from the iterative function
                                if(min_dist < 0.304679){  //the limit is the 95% quantile
                                    connected = 1;
                                    g.connect_nodes(closest_node, connect_node);
                                    g.node_color[closest_node] = Vec3f(0,1,0);
                                    no_connections += 1;
                                    ave_dist_total += min_dist;
                                        median_dist.push_back(min_dist);
                                        
                                }
                            }
                            if(connect_dist > min_dist){ //If conrtains are given, only attach the ones with smaller distances
                                connected = 1;
                                g.connect_nodes(closest_node, connect_node);
                                g.node_color[closest_node] = Vec3f(0,1,0);
                                no_connections += 1;
                                ave_dist_total += min_dist;
                                median_dist.push_back(min_dist);
                            }
                            
                            
                            //Assign distances to the branch thats connected
                            //Right now the branch nodes just all get the same distance as the node we connect to from the skeleton
                            double assign_dist = dist[closest_node];
                            for(auto a: remember_branch){
                                auto rem_node = remember_branch.front();
                                remember_branch.erase(remember_branch.begin());
                                
                                if(connected == 1){ //If the branch ends up beeing connected
                                   dist[rem_node] = assign_dist;
                                }
                            }
                        }
                    }
                }
            }
        }

    
    cout << "_____________________________________" << endl;
    cout << "The ave dist is: " <<  ave_dist_total/no_connections << endl;
    cout << " " << endl;
    sort(median_dist.begin(),median_dist.end());
    if(median_dist.size() != 0){
    cout << "The median is: " << median_dist[(floor(median_dist.size()/2))] <<endl;
    cout << " " << endl;
    cout << "The 75% quantile is: " << median_dist[(floor(median_dist.size()*(0.75)))] <<endl;
    cout << "The 95% quantile is: " << median_dist[(floor(median_dist.size()*(0.95)))] <<endl;
    }

    
    return clean_graph(g);
//    return make_pair(no_connections, g);
    
}



AMGraph3D attach_branches_iteratively(Geometry::AMGraph3D& g, double root_width,  double angle_straight, double angle_complex){
    
    //Vector of distances that we will allow
    queue<double> distance_check;
    distance_check.push(0.1); //0.261
    
    int iterations = 0;
    bool end = false;
    int MAX = 6;
    
    //We iterate as many times as we set checkpoints for distances
    while(!distance_check.empty()){
        iterations += 1;
        cout << "DISTANCE CHECK *********************" << iterations << endl;
        
        double connect = distance_check.front();
        distance_check.pop();
        cout << "current connection distance: " << connect << endl;
        
        //Get distance vector for the graph
        auto a_pair = distance_to_all_nodes(g);
        auto dist = a_pair.first;
        
        //Find the number of loose nodes in the graph
        KDTree<Vec3d, AMGraph3D::NodeID> tree_skeleton;
        KDTree<Vec3d, AMGraph3D::NodeID> tree_branches;

        vector<NodeID> loose;
        Util::AttribVec<NodeID, int> loose_seen(g.no_nodes(),0);  //part of the big skeleton, 0 loose branch, 1 has ben searched
        
        //Color all nodes that can not be reached red
        NodeID lose_nodes = 0;
        NodeID connected_nodes = 0;
        for(auto i = 0; i < g.no_nodes(); i++ ) {
            if(dist[i] == 0){
                g.node_color[i] = Vec3f(1,0,0);
                lose_nodes += 1;
        
                //Create a vector with these LOOSE nodes
                loose.push_back(i);
                tree_branches.insert(g.pos[i], i);
            }
            else{
                connected_nodes += 1;
                tree_skeleton.insert(g.pos[i], i);
               }
        }
        
        tree_skeleton.build();
        tree_branches.build();
        
        
        auto gn = attach_branches(g, connect, angle_straight,angle_complex);
        
        g = gn;
        
    
        if(iterations < MAX){
            distance_check.push(connect*1.2);
        }
        
        
        //If we have meet our max number of iterations we set distance to inf/very big and end
        if(iterations == MAX){
            end = true;
            distance_check.push(100); //100  0.305
            
        }
        
        cout << "______________________________" << endl;
        cout << "NEW DISTANCE" << endl;

        
        
    }
    cout << "_*_*_*_**_*_*" << endl;
    cout << "IN TOTAL WE DID " << iterations << " ITERATIONS" << endl;
    
    return clean_graph(g);
    
}

void color_detached_parts(Geometry::AMGraph3D& g){
    

    
    auto a_pair = distance_to_all_nodes(g);
    auto dist = a_pair.first;
    
    KDTree<Vec3d, AMGraph3D::NodeID> tree_skeleton;
    KDTree<Vec3d, AMGraph3D::NodeID> tree_branches;

    vector<NodeID> loose;
    Util::AttribVec<NodeID, int> loose_seen(g.no_nodes(),0);  //part of the big skeleton, 0 loose branch, 1 has ben searched
    
    for(auto i: g.node_ids()){
        g.node_color[i] = Vec3f(0,0,0);
    }
    
    //Color all nodes that can not be reached red
    NodeID lose_nodes = 0;
    NodeID connected_nodes = 0;
    for(auto i = 0; i < g.no_nodes(); i++ ) {
        if(dist[i] == 0){
            g.node_color[i] = Vec3f(1,0,0);
            lose_nodes += 1;
    
            //Create a vector with these LOOSE nodes
            loose.push_back(i);
            tree_branches.insert(g.pos[i], i);

        }
        else{
            connected_nodes += 1;
            tree_skeleton.insert(g.pos[i], i);
           }
    }
    
    tree_skeleton.build();
    tree_branches.build();
    
    cout << "loose nodes " << lose_nodes << endl;
    cout << "total number " << g.no_nodes() << endl;
}


// ------------------------------
}

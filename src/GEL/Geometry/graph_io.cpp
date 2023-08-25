//
//  graph_io.cpp
//  MeshEditE
//
//  Created by Andreas Bærentzen on 25/01/2020.
//  Copyright © 2020 J. Andreas Bærentzen. All rights reserved.
//

#include <sstream>
#include <fstream>
#include <iostream>

#include <GEL/CGLA/CGLA.h>
#include <GEL/Geometry/KDTree.h>
#include <GEL/Geometry/Graph.h>
#include <GEL/HMesh/HMesh.h>
#include <GEL/Geometry/GridAlgorithm.h>
#include <GEL/Geometry/graph_util.h>
#include <GEL/Geometry/graph_io.h>
#include <GEL/Geometry/rply.h>

using namespace CGLA;
using namespace HMesh;
using namespace std;

namespace Geometry {
    using NodeID = AMGraph::NodeID;
    using NodeSet = AMGraph::NodeSet;


// ----- Edits Helen -----
AMGraph3D graph_load(const std::string& file_name) {
    std::ifstream ifs(file_name);
    AMGraph3D g;
    while (ifs) {
        std::string str;
        getline(ifs, str);
        std::istringstream istr(str);
        char c;
        if (str[0] == 'n') {
            double x, y, z;
            istr >> c >> x >> y >> z;
            NodeID n = g.add_node(Vec3d(x, y, z));
            if (istr >> x >> y >> z) {
                g.node_color[n] = Vec3f(x, y, z);
            }
        } else if (str[0] == 'c') {
            int n0, n1;
            istr >> c >> n0 >> n1;
            g.connect_nodes(n0, n1);
        }
    }
    return g;
}





bool graph_save(const std::string& file_name, const Geometry::AMGraph3D& g) {
    std::ofstream ofs(file_name);

    if (ofs) {
        for (auto n : g.node_ids()) {
            ofs << "n " << g.pos[n][0] << " " << g.pos[n][1] << " " << g.pos[n][2] << " " << g.node_color[n][0] << " " << g.node_color[n][1] << " " << g.node_color[n][2] << std::endl;
        }

        for (auto n : g.node_ids()) {
            for (auto m : g.neighbors(n)) {
                if (n < m) {
                    ofs << "c " << n << " " << m << std::endl;
                }
            }
        }

        return true;
    }

    return false;
}



// ------- Edits Helen -------
AMGraph3D graph_from_points(const string& file_name, double rad, int N_closest)
{
    AMGraph3D g;
           srand(0);
           ifstream f(file_name.c_str());
           string str;
           getline(f, str);
           getline(f, str);
    
    vector<Vec3d> point_cloud;
    
// If the .off file has more columns
    while (getline(f, str)) {
        istringstream istr(str);
        double x, y, z;
        if (istr >> x >> y >> z) {
            Vec3d p(x, y, z);
            point_cloud.push_back(p);
            if (!isnan(p[0])) {
                g.add_node(p);
            } else {
                cout << "nan node not inserted in graph: " << endl;
            }
        } else {
            // Handle error if less than three columns are present
            break;
        }
    }
    
    KDTree<Vec3d, AMGraph3D::NodeID> tree;
    for(auto n : g.node_ids()) {
        Vec3d p = g.pos[n];
        if(isnan(p[0]))
            cout << "nan node inserted in tree: " << n << endl;
        tree.insert(g.pos[n], n);
    }
    
//:::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::
//N_closest = 45;
//    rad = 0.02;
//:::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::
    
    tree.build();
    cout << "Connecting nodes ..." << endl;
    for(auto n : g.node_ids())
    {
        auto nbors = tree.m_closest(N_closest, g.pos[n], rad);
        
//        remove content of loop to not connect nodes
        for(const auto& nn: nbors)
            if(nn.v != n)
                g.connect_nodes(n, nn.v);
//
    }


    
        
//:::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::
    
//    int cnt = 0;
//    cout << "Disconnecting nodes ..." << endl;
//    for(auto n : g.node_ids())
//    {
//        auto nbors = tree.m_closest(N_closest, g.pos[n], rad);
//   :::::::::::
//
//        if(nbors.size()<adjust) {
//            g.remove_node(n);
//            cnt++;
//        }
//        else
//        {
//            Vec3d c = g.pos[n];
//            vector<Vec3d> pts;
//            for(const auto& nn: nbors)
//                if(nn.v != n) {
//                    Vec3d p = g.pos[nn.v];
//                    if(isnan(p[0])) {
//                        cout << "--- Nan: " << endl;
//                        cout << nn.k << " " << nn.v << " " << nn.d << " " << g.pos[n] << endl;
//                    }
//                    else
//                        pts.push_back(p);
//                }
//            Mat3x3d Cov, Q, L;
//            auto mean = covariance(pts, Cov);
//            int no_eig_sols = power_eigensolution(Cov, Q, L);
//
//            if(no_eig_sols==0) {
//                g.remove_node(n);
//                continue;
//            }
//            else if (no_eig_sols==1) {
//                orthogonal(Q[0], Q[1], Q[2]);
//            }
//            else if (no_eig_sols==2) {
//                Q[2] = normalize(cross(Q[0], Q[1]));
//            }
//
//            Vec3d l(L[0][0], L[1][1], L[2][2]);
//            l += Vec3d(0.1);
//            l /= l.max_coord();
//            for(const auto& nn: nbors) {
//                Vec3d v = (g.pos[nn.v]-mean);
//                if (adjust) {
//                    v = Q * v;
//                    v /= l;
//                }
//                if(length(v)>rad) {
//                    auto N = g.neighbors(n);
//                    if(find(begin(N),end(N),nn.v) != end(N)) {
//                        g.disconnect_nodes(n, nn.v);
//                        ++cnt;
//                    }
//                }
//            }
//        }
//
//        :::::::::::::::
//
//    }
//
//    cout << "disconnected " << cnt << endl;

    g = clean_graph(g);
    
    //:::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::
        
    //    Remove all edges that are not contributing to anything, ie delete edge pointers from branches
    
//        cout << "Removing outliers..." << endl;
//        for(auto n : g.node_ids())
//           {
//               float NB = g.neighbors(n).size();
//               if(NB <= 5) {g.remove_node(n); } //5> fjerne
//           }
//
//    saturate
    
//    int hops = 5;
//    int rad1 = 0.05;
//
//    cout << "Saturating..." << endl;
//
//    AMGraph3D g2 = g;
//    double sq_rad = sqr(rad1);
//    for(auto n0: g.node_ids()) {
//        queue<NodeID> Q;
//        Q.push(n0);
//        Util::AttribVec<NodeID, int> H(g.no_nodes(),-1);
//        H[n0] = 0;
//        while(!Q.empty()) {
//            NodeID n = Q.front();
//            Q.pop();
//            int h = H[n];
//            if(h<hops) {
//                const auto& N = g.neighbors(n);
//                for(auto m: N)
//                    if(H[m]==-1 && g.sqr_dist(n0, m)<sq_rad) //
//                    {
//                        g2.connect_nodes(n0, m);
//                        Q.push(m);
//                        H[m] = h+1;
//                    }
//            }
//        }
//
//    }
//    g = g2;
    

    return g;
}



    bool graph_save_ply(const std::string& fn, const AMGraph3D& g) {
        ofstream ofs(fn.c_str());
        if (ofs) {
            auto N = g.no_nodes();
            ofs << "ply" << endl;
            ofs << "format ascii 1.0" << endl;
            ofs << "comment this is a simple file" << endl;
            ofs << "element vertex " << N << endl;
            ofs << "property float x" << endl;
            ofs << "property float y" << endl;
            ofs << "property float z" << endl;
            ofs << "element face 0" << endl;
            ofs << "property list uchar int vertex_indices" << endl;
            ofs << "end_header" << endl;
            for(auto i: g.node_ids())
                ofs << g.pos[i][0] << " " << g.pos[i][1] << " " << g.pos[i][2] << endl;
            return true;
        }
        return false;
    }


    double smooth_step(double tmin, double tmax, double _t) {
        double t = (_t-tmin)/(tmax-tmin);
        t = min(1.0,max(0.0,t));
        return 3*t*t-2*t*t*t;
    }

//IDA's GEL VERSION
void graph_to_mesh_iso(const AMGraph3D& g, Manifold& m, size_t grid_res, float fudge, float tau) {

    Vec3d pmin(1e32), pmax(-1e32);
    for(auto n: g.node_ids())
        if(g.valid_node_id(n)) {
            Vec3d p = g.pos[n];
            if(!isnan(p[0])) {
                pmin = v_min(p, pmin);
                pmax = v_max(p, pmax);
            }
        }
    Vec3d ratios = pmax-pmin;
    double long_side = ratios.max_coord();
    ratios /= long_side;
    Vec3i dim = Vec3i(double(grid_res)*ratios);
    RGrid<float> grid(dim,0.0);
    XForm xform(pmin, pmax, dim, 0.05);

    for(auto n : g.node_ids()) {
        for(auto m : g.neighbors(n))
            if(g.valid_node_id(n) && g.valid_node_id(m) && n<m) {
                LineSegment ls(g.pos[n], g.pos[m]);
                float rad_n = g.node_color[n][1] + fudge;
                float rad_m = g.node_color[m][1] + fudge;
                float rad_upper = 1.5*max(rad_n,rad_m);
                Vec3d bbmin = v_min(g.pos[n],g.pos[m])-Vec3d(rad_upper);
                Vec3d bbmax = v_max(g.pos[n],g.pos[m])+Vec3d(rad_upper);
                Vec3i bbmin_i = v_min(dim - Vec3i(1), v_max(Vec3i(0), Vec3i(xform.apply(bbmin))));
                Vec3i bbmax_i = v_min(dim - Vec3i(1), v_max(Vec3i(0), Vec3i(xform.apply(bbmax))));

//                cout << bbmin << bbmax << bbmin_i << bbmax_i << endl;
                for(size_t zi=bbmin_i[2];zi< bbmax_i[2]; ++zi)
                    for(size_t yi=bbmin_i[1];yi< bbmax_i[1]; ++yi)
                        for(size_t xi=bbmin_i[0];xi< bbmax_i[0]; ++xi) {
                            Vec3i pi(xi, yi, zi);
                            Vec3d p = xform.inverse(Vec3d(pi));
                            auto lp = ls.sqr_distance(p);
                            auto t = smooth_step(0.0, 1.0, lp.t);
                            float rad = rad_n * (1.0 - t) + rad_m * t;
                            grid[pi] = max(grid[pi],float(exp(-2.0*lp.sqr_dist/sqr(rad))));
                        }
            }
    }

    cout << "Done!" << endl;
    cout << "Meshing ..." << endl;

    volume_polygonize(xform, grid, m, tau, false);
    cout << "Done!" << endl;
}


//NEW VERSION
//    void graph_to_mesh_iso(const AMGraph3D& g, Manifold& m, size_t grid_res, float fudge, float tau) {
//
//        double rad_max = 0.0;
//        Vec3d pmin(1e32), pmax(-1e32);
//        for(auto n: g.node_ids())
//            if(g.valid_node_id(n)) {
//                Vec3d p = g.pos[n];
//                double r = g.node_color[n][1];
//                rad_max = max(r, rad_max);
//                if(!std::isnan(p[0])) {
//                    pmin = v_min(p, pmin);
//                    pmax = v_max(p, pmax);
//                }
//            }
//        rad_max += fudge;
//        pmax += Vec3d(rad_max);
//        pmin -= Vec3d(rad_max);
//        Vec3d ratios = pmax-pmin;
//        double long_side = ratios.max_coord();
//        ratios /= long_side;
//        Vec3i dim = Vec3i(double(grid_res)*ratios);
//        RGrid<float> grid(dim,1e32);
//        XForm xform(pmin, pmax, dim, 0.05);
//
//        for(auto n : g.node_ids()) if (g.in_use(n)) {
//            for(auto m : g.neighbors(n))
//                if(n<m) {
//                    LineSegment ls(g.pos[n], g.pos[m]);
//                    float rad_n = g.node_color[n][1] + fudge;
//                    float rad_m = g.node_color[m][1] + fudge;
//                    float rad_upper = 1.5*max(rad_n,rad_m);
//                    Vec3d bbmin = v_min(g.pos[n],g.pos[m])-Vec3d(rad_upper);
//                    Vec3d bbmax = v_max(g.pos[n],g.pos[m])+Vec3d(rad_upper);
//                    Vec3i bbmin_i = v_min(dim - Vec3i(1), v_max(Vec3i(0), Vec3i(xform.apply(bbmin))));
//                    Vec3i bbmax_i = v_min(dim - Vec3i(1), v_max(Vec3i(0), Vec3i(xform.apply(bbmax))));
//
//                    for(Vec3i pi: Range3D(bbmin_i,bbmax_i))  {
//                        Vec3d p = xform.inverse(Vec3d(pi));
//                        auto lp = ls.sqr_distance(p);
//                        auto t = smooth_step(0.0, 1.0, lp.t);
//                        float rad = rad_n * (1.0 - t) + rad_m * t;
//                        grid[pi] = min(grid[pi],float(sqrt(lp.sqr_dist)-rad));
//                    }
//                }
//        }
//
////        GraphDist gd(g);
////
////        for(Vec3i pi: Range3D(Vec3i(0), dim))  {
////            Vec3d p = xform.inverse(Vec3d(pi));
////            grid[pi] = gd.dist(p)-fudge;
////        }
//
//
//        cout << "Done!" << endl;
//        cout << "Meshing ..." << endl;
//        cout << grid.get_dims() << endl;
//        volume_polygonize(xform, grid, m, tau, true, false);
//        cout << "Done!" << endl;
//    }


    void graph_to_mesh_cyl(const AMGraph3D& g, HMesh::Manifold& m, float fudge) {
        m.clear();
        for(auto n: g.node_ids())
            for(auto nn: g.neighbors(n))
                if(n<nn)
                {
                    Vec3d p_n = g.pos[n];
                    double w0 = g.node_color[n][1] + fudge;
                    double w1 = g.node_color[nn][1] + fudge;
                    Vec3d edge_vec = (g.pos[nn] - g.pos[n]);
                    Vec3d X,Y;
                    orthogonal(normalize(edge_vec), X, Y);
                    double len = length(edge_vec);
                    Mat3x3d M = transpose(Mat3x3d(X,Y,normalize(edge_vec)));
                    const int N = 10;
                    double d_alpha =2.0*M_PI/N;
                    for(int i=0;i<N;++i)
                    {
                        float alpha = i * d_alpha;
                        Vec3d p0 = M * Vec3d(w0*cos(alpha), w0*sin(alpha), 0) + p_n;
                        Vec3d p1 = M * Vec3d(w1*cos(alpha), w1*sin(alpha), len) + p_n;
                        Vec3d p2 = M * Vec3d(w0*cos(alpha+d_alpha), w0*sin(alpha+d_alpha), 0) + p_n;
                        Vec3d p3 = M * Vec3d(w1*cos(alpha+d_alpha), w1*sin(alpha+d_alpha), len) + p_n;
                        m.add_face({p0,p2,p3,p1});
                    }
                }
        stitch_mesh(m, 1e-7);
    }

namespace
{
    AMGraph3D *graph;

    int vertex_cb(p_ply_argument argument) {
        static int idx=0;
        static Vec3d p;
        int eol;
        ply_get_argument_user_data(argument, NULL, &eol);
        if(idx<3)
            p[idx] = ply_get_argument_value(argument);
        ++idx;
        if (eol)
        {
            graph->add_node(p);
            idx=0;
        }
        return 1;
    }

    int edge_cb(p_ply_argument argument) {
        static NodeID vertex1;
        int eol;
        ply_get_argument_user_data(argument, NULL, &eol);
        if (eol==0)
            vertex1 = NodeID(ply_get_argument_value(argument));
        else {
            NodeID vertex2 = NodeID(ply_get_argument_value(argument));
            graph->connect_nodes(vertex1, vertex2);
        }
        return 1;
    }
}

bool ply_load(const std::string& fn, AMGraph3D& _graph)
{
    graph = &_graph;
    graph->clear();
    p_ply ply = ply_open(fn.c_str(), NULL);
    if (!ply) return false;
    if (!ply_read_header(ply)) return false;
    ply_set_read_cb(ply, "vertex", "x", vertex_cb, NULL, 0);
    ply_set_read_cb(ply, "vertex", "y", vertex_cb, NULL, 0);
    ply_set_read_cb(ply, "vertex", "z", vertex_cb, NULL, 1);
    ply_set_read_cb(ply, "edge", "vertex1", edge_cb, NULL, 0);
    ply_set_read_cb(ply, "edge", "vertex2", edge_cb, NULL, 1);
    ply_read(ply);
    ply_close(ply);
    return true;
}
}



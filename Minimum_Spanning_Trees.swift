//
//  Minimum_Spanning_Trees.swift
//  DSA self study CommandLine
//
//  Created by sungwook on 11/23/21.
//
// Copyright (c) 2021 by Sungwook Kim
// I created this in Creative Commons (CC BY-NC 4.0).
// https://creativecommons.org/licenses/by-nc/4.0/
// However, anyone who has donated can use it as OPEN SOURCE with ATTRIBUTION ASSURANCE LICENSE.

import Foundation
/// #MST is fundamental problem with diverse applications.
/// ・Dithering.
/// ・Cluster analysis.
/// ・Max bottleneck paths.
/// ・Real-time face verification.
/// ・LDPC codes for error correction.
/// ・Image registration with Renyi entropy.
/// ・Find road networks in satellite and aerial imagery.
/// ・Reducing data storage in sequencing amino acids in a protein.
/// ・Model locality of particle interactions in turbulent fluid flows.
/// ・Autoconfig protocol for Ethernet bridging to avoid cycles in a network.
/// ・Approximation algorithms for NP-hard problems (e.g., TSP, Steiner tree).
/// ・Network design (communication, electrical, hydraulic, computer, road).

/// Minimum spanning tree in PRIM algorithm, a greedy algorithm
/// key holds the minimum weight per vertex.
///
/// time complexity O(V^2)
public func PRIMs_algorithm_of_MST__greedy_algorithm(_ G: [[Int]], verbose: Bool = false) -> [Int] {
    guard G.count >= 2 else {
        return .init()
    }
    /// E(u,v) = E(i, mst[i])
    var MST = Array(repeating: 0, count: G.count)
    var visited = Array(repeating: false, count: G.count)  /// `requirement 1st` as `set MST`
    let V = G.count
    var keys_of_PRIM = Array(repeating: Int.max, count: V)  /// `requirement 2nd`
    /// key at vertex 0 already holds a minimum weight
    ///  so that the search will start from vertex 0.
    keys_of_PRIM[0] = 0
    
    let index_of_min = { (visited: [Bool], key: [Int]) -> Int in
        /// For key[0] = 0, it is highly likely that index_of_min == 0
        var min_value = Int.max, index_of_min = 0
        for u in 0..<G.count {
            if visited[u] == false, key[u] < min_value {
                min_value = key[u]
                index_of_min = u
            }
        }
        return index_of_min
    }
    
    /// Because `peers` will have G.count vertices, the number iteration should be G.count.
    for _ in 0..<G.count {
        let u = index_of_min(visited, keys_of_PRIM)
        visited[u] = true /// `<--`
        verbose ? print("u = \(u)"):()
        for v in 0..<G.count {
            /// G[u][v] == 0 means that there are no such edge E(u, v).
            if visited[v] == false, G[u][v] > 0, G[u][v] < keys_of_PRIM[v] { /// `<--`
                keys_of_PRIM[v] = G[u][v] /// `1 <--`
                MST[v] = u /// `2 <--`
            }
        }
        verbose ? print("MST = \(MST)"):()
    }
    return MST
}


/// In order to utilize minimum priority queue properly, I defined two functions == and < only considering the value of `key`.
/// The MPQ shall have its own index while retaining the index and key as VertexKeyPair.
fileprivate struct KeyCentric_IKeyPair: Comparable & Equatable {
    /// vertex number
    let i: Int
    /// key value
    var key: Int
    static func == (l: KeyCentric_IKeyPair, r: KeyCentric_IKeyPair) -> Bool {
        l.key == r.key
    }
    static func < (l: KeyCentric_IKeyPair, r: KeyCentric_IKeyPair) -> Bool {
        l.key < r.key
    }
    func isEqualAll(l: KeyCentric_IKeyPair, r: KeyCentric_IKeyPair) -> Bool {
        l.i == r.i && l.key == r.key
    }
}

/// Minimum spanning tree in PRIM algorithm using Minimum Priority Queue.
///
/// There is a catch due to the limit of implementation, I had to employ `VertexKeyPair`.
/// Shall it be a better solution in performance?
/// And this is dependent upon `MinPriorityQueue`
///
/// time complexity O(ElogV), faster than the rigorous method as V gets larger.
public func PRIMs_algorithm_of_MST_by_MinPriorityQueue(_ G: [[Int]], verbose: Bool = false) -> [Int] {
    guard G.count >= 2 else {
        return .init()
    }
    /// E(u,v) = E(i, mst[i])
    var MST = Array(repeating: 0, count: G.count)
    var visited = Array(repeating: false, count: G.count) /// `requirement 1st`
    let picked_vertex = 0
    visited[picked_vertex] = true
    /// I paralleled key and mpq in the implementation.
    var key = Array(repeating: Int.max, count: G.count)  /// `requirement 2nd`
    key[0] = 0
    /// tempArr for setting `mpq`.
    var tempArr = [KeyCentric_IKeyPair]()
    (0..<G.count).forEach {
        $0 == picked_vertex ? tempArr.append(KeyCentric_IKeyPair(i: $0, key: 0)) : tempArr.append(KeyCentric_IKeyPair(i: $0, key: Int.max))
    }
    var mpq = MinPriorityQueue(keys: tempArr)  /// `requirement 3rd`
    
    for _ in G.startIndex..<G.endIndex {
        let u = mpq.extractMin()!
        verbose ? print("u = \(u)"):()
        visited[u.i] = true /// `<--`
        var count_when_the_updated_key_and_min_the_same = 0, count_when_the_updated_key_and_min_are_unrelevant = 0
        /// adj list was simplified according to the situation
        /// that is crucial in CP.
        for v in G.startIndex..<G.endIndex {
            /// G[u][v] == 0 means that there are no such edge E(u, v).
            if G[u.i][v] > 0, visited[v] == false, G[u.i][v] < key[v] { /// `<--`
                /// #CAVEAT
                /// This portion O(unvisited_V*E log(V)) determines the overall performance, more away from time complexity O(E log(V))
                guard let index_for_mpq = mpq.heap.keys.firstIndex(where: { $0.i == v }) else {
                    fatalError("If you see this message, it means that the code above should have faulty logic.")
                }
                // MARK: An impossible attempt to improve more performance than O(V) because there is no definitive structural rules to find the mpq index by `the value of the key`.
                // MARK: A catch - the value of keys can be not unique.
                // MARK: Due to KeyCentric_IKeyPair, the real i was disregarded in < and == operators.
                /// let key_of_mpq = KeyCentric_IKeyPair(i: v, key: key[v])
                /// guard let firstIndex_for_mpq = mpq.heap.firstIndex(of: key_of_mpq) else {
                ///     fatalError("If you see this message, it means that the code above should have faulty logic.")
                /// }
                /// guard let index_2nd_for_mpq: Int = Array(mpq.heap.keys.startIndex...firstIndex_for_mpq).firstIndex(where: { mpq.heap.keys[$0].key == key[v] && mpq.heap.keys[$0].i == v }) else {
                ///     fatalError("If you see this message, it means that the code above should have faulty logic.")
                /// }
                /// assert(index_for_mpq == index_2nd_for_mpq) /// --> therefore, not always true.
                MST[v] = u.i /// `1 <--`
                key[v] = G[u.i][v] /// `2 <--`
                verbose ? print("mpq_i = \(index_for_mpq), v = \(v)"):()
                mpq.changePriority(index_for_mpq, KeyCentric_IKeyPair(i: v, key: key[v])) /// `3 <--`
                key[v] == mpq.min?.key && verbose ? {count_when_the_updated_key_and_min_the_same += 1}():{ count_when_the_updated_key_and_min_are_unrelevant += 1}()
            }
        }
        verbose ? {print("count_when_the_updated_key_and_min_the_same = \(count_when_the_updated_key_and_min_the_same), count_when_the_updated_key_and_min_are_unrelevant = \(count_when_the_updated_key_and_min_are_unrelevant)")}():{}()
        /// Finding:
        verbose ? print("MST = \(MST)"):()
    }
    return MST
}


/// Dijkstra's shortest path algorithm, Adjacency Matrix Representation, Greedy Algorithm
///
/// time complexity O(V^2)
public func Dijkstras_algorithm_of_shortest_path_matrix__greedy_algorithm(_ G: [[Int]], source_index: Int, verbose: Bool = false) -> (path: [Int], dist: [Int]) {
    guard G.count >= 2 else {
        return (.init(), .init())
    }
    /// E(u,v) = E(i, mst[i])
    var path = Array(repeating: 0, count: G.count)
    var visited = Array(repeating: false, count: G.count)  /// `requirement 1st` as `set MST`
    var dist_of_Dijkstra = Array(repeating: Int.max, count: G.count)  /// `requirement 2nd`
    /// key at vertex `source_index` already holds a minimum weight
    ///  so that the search will start from vertex 0.
    dist_of_Dijkstra[source_index] = 0
    let index_of_min = { (visited: [Bool], dist: [Int]) -> Int in
        var index_min = source_index, min = Int.max
        for v in 0..<G.count {
            if visited[v] == false, dist[v] < min {
                min = dist[v]; index_min = v
            }
        }
        return index_min
    }
    for _ in 0..<G.count {
        let u = index_of_min(visited, dist_of_Dijkstra)
        visited[u] = true
        for v in 0..<G.count {
            /// I think the modified code is better.
            //            if G[u][v] > 0, visited[v] == false, dist_of_Dijkstra[u] != Int.max, G[u][v] + dist_of_Dijkstra[u] < dist_of_Dijkstra[v] {
            if G[u][v] > 0, visited[v] == false, G[u][v] + dist_of_Dijkstra[u] < dist_of_Dijkstra[v] {
                dist_of_Dijkstra[v] = dist_of_Dijkstra[u] + G[u][v]
                path[v] = u
            }
        }
    }
    return (path: path, dist: dist_of_Dijkstra)
}

func test__PRIM_MST(verbose: Bool = false) {
    var Gs = [
        [
            [0, 9, 75, 0, 0],
            [9, 0, 95, 19, 42],
            [75, 95, 0, 51, 66],
            [0, 19, 51, 0, 31],
            [0, 42, 66, 31, 0],
        ],
        [
            [ 0, 2, 0, 6, 0 ],
            [ 2, 0, 3, 8, 5 ],
            [ 0, 3, 0, 0, 7 ],
            [ 6, 8, 0, 0, 9 ],
            [ 0, 5, 7, 9, 0 ],
        ],
        /** Let us create the following graph
         2     3
         (0)--(1)--(2)
         |    / \    |
         6| 8/   \5  |7
         |  /     \  |
         (3)-------(4)
         9
         */
        [ /// 9x9 matrix
            [0, 4,  0,   0,  0,  0, 0,  8,  0],
            [4, 0,  8,   0,  0,  0, 0, 11,  0],
            [0, 8,  0,   7,  0,  4, 0,  0,  2],
            [0, 0,  7,   0,  9, 14, 0,  0,  0],
            [0, 0,  0,   9,  0, 10, 0,  0,  0],
            [0, 0,  4,  14, 10,  0, 2,  0,  0],
            [0, 0,  0,   0,  0,  2, 0,  1,  6],
            [8, 11, 0,   0,  0,  0, 1,  0,  7],
            [0, 0,  2,   0,  0,  0, 6,  7,  0],
        ],
        /// addEdge(graph, 0, 1, 4);
        /// addEdge(graph, 0, 7, 8);
        /// addEdge(graph, 1, 2, 8);
        /// addEdge(graph, 1, 7, 11);
        /// addEdge(graph, 2, 3, 7);
        /// addEdge(graph, 2, 8, 2);
        /// addEdge(graph, 2, 5, 4);
        /// addEdge(graph, 3, 4, 9);
        /// addEdge(graph, 3, 5, 14);
        /// addEdge(graph, 4, 5, 10);
        /// addEdge(graph, 5, 6, 2);
        /// addEdge(graph, 6, 7, 1);
        /// addEdge(graph, 6, 8, 6);
        /// addEdge(graph, 7, 8, 7);
        
        [ /// 9x9 matrix
            [ 0, 4, 0, 0, 0, 0, 0, 8, 0 ],
            [ 4, 0, 8, 0, 0, 0, 0, 11, 0 ],
            [ 0, 8, 0, 7, 0, 4, 0, 0, 2 ],
            [ 0, 0, 7, 0, 9, 14, 0, 0, 0 ],
            [ 0, 0, 0, 9, 0, 10, 0, 0, 0 ],
            [ 0, 0, 4, 14, 10, 0, 2, 0, 0],
            [ 0, 0, 0, 0, 0, 2, 0, 1, 6 ],
            [ 8, 11, 0, 0, 0, 0, 1, 0, 7 ],
            [ 0, 0, 2, 0, 0, 0, 6, 7, 0 ]
        ],
        [
            [0, 4, 0, 0, 0, 0, 0, 8, 0, 4, 0, 0, 0, 0, 0, 8, 0, 1],
            [4, 0, 8, 0, 0, 0, 0, 11, 0, 8, 0, 0, 0, 0, 11, 0, 9, 2],
            [0, 8, 0, 7, 0, 4, 0, 0, 2, 0, 8, 0, 7, 0, 4, 0, 0, 2],
            [0, 0, 7, 0, 9, 14, 0, 0, 0, 0, 0, 7, 0, 9, 14, 0, 0, 0],
            [0, 0, 0, 9, 0, 10, 0, 0, 0, 0, 0, 0, 9, 0, 10, 0, 0, 0],
            [0, 0, 4, 14, 10, 0, 2, 0, 0, 0, 0, 4, 14, 10, 0, 2, 0, 0],
            [0, 0, 0, 0, 0, 2, 0, 1, 6, 0, 0, 0, 0, 0, 2, 0, 1, 6],
            [8, 11, 0, 0, 0, 0, 1, 0, 7, 8, 11, 0, 0, 0, 0, 1, 0, 7],
            [0, 0, 2, 0, 0, 0, 6, 7, 0, 0, 0, 2, 0, 0, 0, 6, 7, 0],
            [4, 8, 0, 0, 0, 0, 0, 8, 0, 0, 0, 2, 0, 0, 0, 6, 7, 0],
            [0, 0, 8, 0, 0, 0, 0, 11, 0, 0, 0, 2, 0, 0, 0, 6, 7, 0],
            [0, 0, 0, 7, 0, 4, 0, 0, 2, 2, 2, 0, 0, 0, 0, 6, 7, 0],
            [0, 0, 7, 0, 9, 14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 0, 1],
            [0, 0, 0, 9, 0, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 0, 2],
            [0, 11, 4, 14, 10, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 8, 0, 3],
            [8, 0, 0, 0, 0, 2, 0, 1, 6, 6, 6, 6, 8, 8, 8, 0, 8, 4],
            [0, 9, 0, 0, 0, 0, 1, 0, 7, 7, 7, 7, 0, 0, 0, 8, 0, 5],
            [1, 2, 2, 0, 0, 0, 6, 7, 0, 0, 0, 0, 1, 2, 3, 4, 5, 0],
        ],
    ]
    var answers = [ 110, 16, 37, 37, 42 ]
    
    /// The graph drawn in the picture here.
    let G_in_edge_set = [
        (u: 0, v: 1, weight: 4),
        (0, 2, 6), (0, 3 , 16), (1, 5, 24), (2, 5, 23), (2, 3, 8), (2, 4, 5),
        (3, 4, 10), (3, 7, 21), (4, 7, 14), (4, 6, 11), (4, 5, 18), (4, 6, 11), (5, 6, 9), (6, 7, 7)
    ]
    var G_in_matrix_8x8 = Array(repeating: Array(repeating: 0, count: 8), count: 8)
    for edge in G_in_edge_set {
        G_in_matrix_8x8[edge.0][edge.1] = edge.2
    }
    for i in 0..<G_in_matrix_8x8.count {
        for j in 0..<G_in_matrix_8x8.first!.count {
            if G_in_matrix_8x8[i][j] > 0 {
                G_in_matrix_8x8[j][i] = G_in_matrix_8x8[i][j]
            } else if G_in_matrix_8x8[j][i] > 0 {
                G_in_matrix_8x8[i][j] = G_in_matrix_8x8[j][i]
            }
        }
    }
    /// insert it just after 5x5
    Gs.insert(G_in_matrix_8x8, at: 2)
    answers.insert(50, at: 2)
    
    /// check the Integrity of answers and Gs
    assert(Gs.count == answers.count)
    for (G, ans) in zip(Gs, answers) {
        /// check the Integrity of G.
        var Corrected_G = G
        for i in 0..<G.count {
            assert(G.count == G[i].count)
            for j in 0..<G.first!.count {
                if G[i][j] != G[j][i] {
                    assert(G[i][j] == G[j][i])
                    Corrected_G[j][i] = Corrected_G[i][j]
                    print("WRONG i, j = \(i), \(j)")
                }
                if i == j {
                    assert(G[i][j] == 0)
                    Corrected_G[i][j] = 0
                }
            }
        }
        if G != Corrected_G {
            print("Corrected GG:")
            Corrected_G.forEach { print($0, terminator: ",\n") }
        }
        assert(G == Corrected_G)
        
        repeatElement(0, count: 60).forEach { _ in print("=", terminator: "") }; print("")
        print("G = a graph in \(G.count) x \(G.first!.count) matrix representation")
        G.forEach { print($0, terminator: ",\n") }
        
        // MARK: - Time Complexity O(VxV)
        print("Time Complexity O(VxV):")
        var start_time: Date, end_time: Date
        start_time = Date()
        var mst = PRIMs_algorithm_of_MST__greedy_algorithm(G, verbose: verbose)
        end_time = Date()
        let diff_of_VxV = end_time.timeIntervalSinceReferenceDate - start_time.timeIntervalSinceReferenceDate
        print("For G =")
        G.forEach { print($0) }
        for i in (G.startIndex+1)..<G.endIndex {
            print("\(i) -- \(mst[i]) has weight \(G[i][mst[i]])")
        }
        var total_weight_of_MST = ((G.startIndex+1)..<G.endIndex).map { G[$0][mst[$0]] }.reduce(0, +)
        print("total_weight_of_MST = \(total_weight_of_MST)"); print("")
        
        verbose ? print("mst = \(mst)"):()
        assert(total_weight_of_MST == ans)
        
        // MARK: - Time Complexity O(E Log(V)) by MinPriorityQueue
        print("Time Complexity O(E Log(V)) by MinPriorityQueue:")
        start_time = Date()
        mst = PRIMs_algorithm_of_MST_by_MinPriorityQueue(G, verbose: verbose)
        end_time = Date()
        let diff_MPG = end_time.timeIntervalSinceReferenceDate - start_time.timeIntervalSinceReferenceDate
        print("For G =")
        G.forEach { print($0, terminator: ",\n") }
        for i in (G.startIndex+1)..<G.endIndex {
            print("\(i) -- \(mst[i]) has weight \(G[i][mst[i]])")
        }
        total_weight_of_MST = ((G.startIndex+1)..<G.endIndex).map { G[$0][mst[$0]] }.reduce(0, +)
        print("total_weight_of_MST from PRIMs_algorithm_of_MST_by_MinPriorityQueue = \(total_weight_of_MST)")
        
        // MARK: - Verdict
        print("PRIMs_algorithm_of_MST_by_MinPriorityQueue is \(String(format: "%.2f",diff_of_VxV/diff_MPG)) times faster than PRIMs_algorithm_of_MST_by_VXV_Matrix")
        
        print("\n")
        verbose ? print("mst = \(mst)"):()
        assert(total_weight_of_MST == ans)
        
        // MARK: - Dijkstra's shortest path
        print("")
        let path_and_dist = Dijkstras_algorithm_of_shortest_path_matrix__greedy_algorithm(G, source_index: 0, verbose: true)
        print("Dijkstra's shortest path:")
        path_and_dist.path.enumerated().forEach {
            print("\($0.offset) -- \($0.element)")
        }
        print("Vertex   Distance from Source:")
        path_and_dist.dist.enumerated().forEach {
            print("\($0.offset) -- \($0.element)")
        }
        print("The total of the shorted distance from 0 = \(path_and_dist.dist.reduce(0, +))")
    }
    
}

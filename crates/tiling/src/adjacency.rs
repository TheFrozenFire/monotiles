use crate::metatile::{
    InflationRule, MetatileType, BOUNDARY_CHILDREN, SUPERTILE_F_CHILDREN, SUPERTILE_H_CHILDREN,
    SUPERTILE_P_CHILDREN, SUPERTILE_T_CHILDREN,
};

/// An adjacency edge between two children within an inflation.
///
/// Two children are adjacent if one is placed relative to the other
/// via an `Adjacent` or `Bridge` rule, meaning they share a vertex.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ChildAdjacency {
    /// Index of the neighbor child (0..28).
    pub neighbor: usize,
    /// The vertex index on the current child that is shared.
    pub self_vertex: usize,
    /// The vertex index on the neighbor that is shared.
    pub neighbor_vertex: usize,
}

/// The complete adjacency graph of children within a single H-supertile inflation.
///
/// Built from the 29 inflation rules: each `Adjacent` or `Bridge` rule creates
/// adjacency edges between the newly placed child and its reference parent(s).
#[derive(Clone, Debug)]
pub struct InflationAdjacency {
    /// For each child index 0..28, the list of adjacent children.
    pub adjacencies: Vec<Vec<ChildAdjacency>>,
    /// The metatile type of each child.
    pub child_types: Vec<MetatileType>,
}

impl InflationAdjacency {
    /// Which supertile type (if any) a given child index is assigned to.
    pub fn assigned_supertile(&self, child_index: usize) -> Option<(MetatileType, usize)> {
        for (st, children) in [
            (MetatileType::H, SUPERTILE_H_CHILDREN),
            (MetatileType::T, SUPERTILE_T_CHILDREN),
            (MetatileType::P, SUPERTILE_P_CHILDREN),
            (MetatileType::F, SUPERTILE_F_CHILDREN),
        ] {
            if let Some(pos) = children.iter().position(|&c| c == child_index) {
                return Some((st, pos));
            }
        }
        None
    }

    /// Whether a child index is a boundary child.
    pub fn is_boundary(&self, child_index: usize) -> bool {
        BOUNDARY_CHILDREN.contains(&child_index)
    }

    /// Get the neighbors of a child that belong to a specific supertile.
    pub fn neighbors_in_supertile(
        &self,
        child_index: usize,
        supertile_children: &[usize],
    ) -> Vec<&ChildAdjacency> {
        self.adjacencies[child_index]
            .iter()
            .filter(|adj| supertile_children.contains(&adj.neighbor))
            .collect()
    }
}

/// Build the internal adjacency graph from the 29 inflation rules.
///
/// Each `Adjacent { parent, vertex, child_type, child_vertex }` rule means:
/// - The new child shares `vertex` on `parent` with `child_vertex` on itself
/// - This creates a bidirectional adjacency edge between parent and child
///
/// Each `Bridge { parent_a, vertex_a, parent_b, vertex_b, child_type, child_vertex }` rule means:
/// - The new child is placed using two reference parents
/// - It shares vertex_a with parent_a and connects near parent_b
/// - Creates adjacency edges between the new child and both parents
pub fn inflation_adjacency() -> InflationAdjacency {
    let rules = crate::metatile::inflation_rules();
    let n = rules.len(); // 29

    let mut adjacencies: Vec<Vec<ChildAdjacency>> = vec![Vec::new(); n];
    let mut child_types = Vec::with_capacity(n);

    for (child_idx, rule) in rules.iter().enumerate() {
        match rule {
            InflationRule::Seed(t) => {
                child_types.push(*t);
            }
            InflationRule::Adjacent {
                parent,
                vertex,
                child_type,
                child_vertex,
            } => {
                child_types.push(*child_type);

                // Bidirectional adjacency: parent <-> child
                adjacencies[*parent].push(ChildAdjacency {
                    neighbor: child_idx,
                    self_vertex: *vertex,
                    neighbor_vertex: *child_vertex,
                });
                adjacencies[child_idx].push(ChildAdjacency {
                    neighbor: *parent,
                    self_vertex: *child_vertex,
                    neighbor_vertex: *vertex,
                });
            }
            InflationRule::Bridge {
                parent_a,
                vertex_a,
                parent_b,
                vertex_b,
                child_type,
                child_vertex,
            } => {
                child_types.push(*child_type);

                // Child is adjacent to parent_a via vertex_a <-> child_vertex
                adjacencies[*parent_a].push(ChildAdjacency {
                    neighbor: child_idx,
                    self_vertex: *vertex_a,
                    neighbor_vertex: *child_vertex,
                });
                adjacencies[child_idx].push(ChildAdjacency {
                    neighbor: *parent_a,
                    self_vertex: *child_vertex,
                    neighbor_vertex: *vertex_a,
                });

                // Child is also adjacent to parent_b via vertex_b
                // The child_vertex for parent_b connection isn't directly specified,
                // but we know parent_b is a reference point. We record it with
                // a secondary vertex relationship.
                adjacencies[*parent_b].push(ChildAdjacency {
                    neighbor: child_idx,
                    self_vertex: *vertex_b,
                    neighbor_vertex: *child_vertex,
                });
                adjacencies[child_idx].push(ChildAdjacency {
                    neighbor: *parent_b,
                    self_vertex: *child_vertex,
                    neighbor_vertex: *vertex_b,
                });
            }
        }
    }

    InflationAdjacency {
        adjacencies,
        child_types,
    }
}

/// Information about a boundary child's external connections.
///
/// Boundary children are shared between adjacent supertiles. This struct
/// describes which supertile types a boundary child connects to internally
/// (within the current inflation) and which children it is adjacent to.
#[derive(Clone, Debug)]
pub struct BoundaryConnection {
    /// The boundary child index (one of [5, 12, 13, 14, 17, 18, 19]).
    pub child_index: usize,
    /// The metatile type of this boundary child.
    pub child_type: MetatileType,
    /// Adjacent children that are assigned to supertiles (not boundary).
    pub internal_neighbors: Vec<(usize, MetatileType)>,
    /// Adjacent children that are also boundary.
    pub boundary_neighbors: Vec<(usize, MetatileType)>,
}

/// For each boundary child, identify its connections within the inflation.
///
/// This is needed for recognizability: boundary children connect supertiles,
/// and their neighborhoods must be accounted for when composing metatiles
/// into supertiles during deflation.
pub fn boundary_connections() -> Vec<BoundaryConnection> {
    let adj = inflation_adjacency();

    BOUNDARY_CHILDREN
        .iter()
        .map(|&child_idx| {
            let child_type = adj.child_types[child_idx];
            let mut internal_neighbors = Vec::new();
            let mut boundary_neighbors = Vec::new();

            for neighbor_adj in &adj.adjacencies[child_idx] {
                let neighbor_type = adj.child_types[neighbor_adj.neighbor];
                if adj.is_boundary(neighbor_adj.neighbor) {
                    boundary_neighbors.push((neighbor_adj.neighbor, neighbor_type));
                } else {
                    internal_neighbors.push((neighbor_adj.neighbor, neighbor_type));
                }
            }

            BoundaryConnection {
                child_index: child_idx,
                child_type,
                internal_neighbors,
                boundary_neighbors,
            }
        })
        .collect()
}

/// Check if the assigned children of a given supertile form a connected subgraph.
pub fn is_supertile_connected(supertile_children: &[usize]) -> bool {
    if supertile_children.is_empty() {
        return true;
    }

    let adj = inflation_adjacency();
    let child_set: std::collections::HashSet<usize> = supertile_children.iter().copied().collect();

    // BFS from the first child
    let mut visited = std::collections::HashSet::new();
    let mut queue = std::collections::VecDeque::new();
    queue.push_back(supertile_children[0]);
    visited.insert(supertile_children[0]);

    while let Some(current) = queue.pop_front() {
        for neighbor_adj in &adj.adjacencies[current] {
            if child_set.contains(&neighbor_adj.neighbor) && visited.insert(neighbor_adj.neighbor) {
                queue.push_back(neighbor_adj.neighbor);
            }
        }
    }

    visited.len() == child_set.len()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn adjacency_graph_has_29_nodes() {
        let adj = inflation_adjacency();
        assert_eq!(adj.adjacencies.len(), 29);
        assert_eq!(adj.child_types.len(), 29);
    }

    #[test]
    fn adjacency_is_symmetric() {
        let adj = inflation_adjacency();
        for (i, neighbors) in adj.adjacencies.iter().enumerate() {
            for n in neighbors {
                let reverse = adj.adjacencies[n.neighbor]
                    .iter()
                    .any(|rev| rev.neighbor == i);
                assert!(
                    reverse,
                    "adjacency {}->{} is not symmetric",
                    i, n.neighbor
                );
            }
        }
    }

    #[test]
    fn seed_has_expected_neighbors() {
        let adj = inflation_adjacency();
        // Child 0 is the seed (H). From the rules:
        // 1: Adjacent { parent: 0, vertex: 0, ... } -> child 0 is adjacent to child 1
        // 6: Adjacent { parent: 0, vertex: 4, ... } -> child 0 is adjacent to child 6
        // 27: Bridge { parent_a: 9, ..., parent_b: 0, vertex_b: 2, ... } -> child 0 adj to 27
        let neighbors: Vec<usize> = adj.adjacencies[0].iter().map(|a| a.neighbor).collect();
        assert!(neighbors.contains(&1), "seed should be adjacent to child 1");
        assert!(neighbors.contains(&6), "seed should be adjacent to child 6");
        assert!(
            neighbors.contains(&27),
            "seed should be adjacent to child 27"
        );
    }

    #[test]
    fn child_types_match_inflation_rules() {
        let adj = inflation_adjacency();
        let rules = crate::metatile::inflation_rules();

        for (i, rule) in rules.iter().enumerate() {
            let expected = match rule {
                InflationRule::Seed(t) => *t,
                InflationRule::Adjacent { child_type, .. } => *child_type,
                InflationRule::Bridge { child_type, .. } => *child_type,
            };
            assert_eq!(adj.child_types[i], expected, "type mismatch at child {}", i);
        }
    }

    #[test]
    fn boundary_children_have_connections() {
        let connections = boundary_connections();
        assert_eq!(connections.len(), 7);

        for conn in &connections {
            assert!(
                BOUNDARY_CHILDREN.contains(&conn.child_index),
                "child {} should be a boundary child",
                conn.child_index
            );
            // Each boundary child should have at least one neighbor (internal or boundary)
            let total = conn.internal_neighbors.len() + conn.boundary_neighbors.len();
            assert!(
                total > 0,
                "boundary child {} should have at least one neighbor",
                conn.child_index
            );
        }
    }

    #[test]
    fn placement_tree_spans_all_children() {
        // The inflation rules form a spanning tree: every non-seed child
        // is placed relative to at least one previously placed child.
        // This means every child (except the seed) has at least one neighbor
        // in the placement tree.
        let adj = inflation_adjacency();
        for i in 1..29 {
            assert!(
                !adj.adjacencies[i].is_empty(),
                "child {} should have placement neighbors",
                i
            );
        }
    }

    #[test]
    fn all_29_children_reachable_from_seed() {
        // The placement tree connects all 29 children starting from the seed.
        let adj = inflation_adjacency();
        let mut visited = std::collections::HashSet::new();
        let mut queue = std::collections::VecDeque::new();
        queue.push_back(0usize);
        visited.insert(0usize);

        while let Some(current) = queue.pop_front() {
            for neighbor_adj in &adj.adjacencies[current] {
                if visited.insert(neighbor_adj.neighbor) {
                    queue.push_back(neighbor_adj.neighbor);
                }
            }
        }

        assert_eq!(
            visited.len(),
            29,
            "all 29 children should be reachable from seed"
        );
    }

    #[test]
    fn every_assigned_child_is_adjacent_to_something() {
        let adj = inflation_adjacency();
        let all_assigned: Vec<usize> = SUPERTILE_H_CHILDREN
            .iter()
            .chain(SUPERTILE_T_CHILDREN)
            .chain(SUPERTILE_P_CHILDREN)
            .chain(SUPERTILE_F_CHILDREN)
            .copied()
            .collect();

        for &child in &all_assigned {
            assert!(
                !adj.adjacencies[child].is_empty(),
                "assigned child {} should have at least one neighbor",
                child
            );
        }
    }

    #[test]
    fn assigned_supertile_lookup() {
        let adj = inflation_adjacency();

        // Child 0 is in H supertile
        assert_eq!(
            adj.assigned_supertile(0),
            Some((MetatileType::H, 0))
        );

        // Child 11 is in T supertile
        assert_eq!(
            adj.assigned_supertile(11),
            Some((MetatileType::T, 0))
        );

        // Child 5 is a boundary child
        assert_eq!(adj.assigned_supertile(5), None);
        assert!(adj.is_boundary(5));
    }
}

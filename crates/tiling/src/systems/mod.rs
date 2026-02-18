pub mod hat;
pub mod hat_turtle;
pub mod spectre;

/// Abstraction over a hierarchical substitution tiling system.
///
/// Each system defines a set of tile types, an inflation rule that expands
/// each tile into children, and how those children group into supertiles.
/// This enables generic analysis (one-way, vulnerability, substitution)
/// across hat, spectre, and hat-turtle tilings.
pub trait TilingSystem: Send + Sync {
    fn name(&self) -> &str;
    fn num_types(&self) -> usize;
    fn type_name(&self, index: usize) -> &str;
    fn supertile_name(&self, index: usize) -> &str;

    /// Total inflation children (29 for hat, 15 for spectre).
    fn num_inflation_children(&self) -> usize;
    /// Type index of each inflation child.
    fn inflation_child_type(&self, child: usize) -> usize;
    /// Which children belong to supertile type `type_index`.
    fn supertile_children(&self, type_index: usize) -> &[usize];
    /// Boundary children not assigned to any supertile.
    fn boundary_children(&self) -> &[usize];

    /// Composition matrix: `composition()[i][j]` = count of type j in supertile i.
    fn composition(&self) -> &[Vec<usize>];
    /// Inflation adjacency: for each child, list of neighbor child indices.
    fn inflation_adjacency(&self) -> &[Vec<usize>];

    /// Whether inflation reverses tile orientation (true for spectre).
    fn reverses_orientation(&self) -> bool {
        false
    }
    /// Whether the system uses reflected tiles.
    fn uses_reflections(&self) -> bool {
        false
    }
}

/// Resolve a tiling system by name.
pub fn resolve_system(name: &str) -> anyhow::Result<Box<dyn TilingSystem>> {
    match name.to_lowercase().as_str() {
        "hat" => Ok(Box::new(hat::HatSystem::new())),
        "spectre" => Ok(Box::new(spectre::SpectreSystem::new())),
        "hat-turtle" | "hat_turtle" => Ok(Box::new(hat_turtle::HatTurtleSystem::default())),
        _ => anyhow::bail!(
            "Unknown tiling system: '{}'. Valid: hat, spectre, hat-turtle",
            name
        ),
    }
}

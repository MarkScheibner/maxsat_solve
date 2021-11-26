use std::io::{self, BufRead };
use std::time::Instant;
use std::collections::HashSet;
use metrohash::MetroHashSet;
use itertools::Itertools;
use bit_set::BitSet;
use anyhow::bail;
use rand::{ rngs::StdRng, SeedableRng, prelude::IteratorRandom };

//
// Computes a tree decomposition in time $O(n k^2)$, where $k$ is
// the computed width.
//

/// Seed of the random number generator.
pub const SEED: u64 = 42;

/// A tree decomposition is stored as (rooted) tree:
/// Each node has a unique parent (or points to itself, if it is the root)
/// and stores a bag. Thus, we can store the whole decomposition as array of
/// tuples (the parent and the bag content).
///
pub type Decomposition = Vec<(usize, Vec<usize>)>;

pub struct Graph {
    n:         usize,                    // universe size ($V=\{0,\dots,1\}$)
    neighbors: Vec<MetroHashSet<usize>>, // edge set of the graph
}

impl Graph {

    pub fn new(n: usize) -> Graph {
        Graph { n, neighbors: vec![MetroHashSet::default(); n] }
    }
    
    pub fn add_edge(&mut self, u: usize, v: usize) {
        self.neighbors[u].insert(v);
        self.neighbors[v].insert(u);
    }

    /// Eliminates the given vertex:
    /// - remove if from the neighborhood of its neighbors
    /// - make its neighborhood a clique
    ///
    fn eliminate_vertex(&mut self, v: usize) {
        let bag = self.neighbors[v].clone();
        bag.iter().for_each(|&x| {self.neighbors[x].remove(&v);} );
        bag.iter().tuple_combinations().for_each(|(&x, &y)| self.add_edge(x, y));
    }

    /// Compute a perfect elimination order of a chordal graph $H$ that is greedily constructed from *G*.
    /// The construction is in-place, so *G* will be destroyed and replaced by *H*.
    ///
    pub fn compute_peo(&mut self, rng: &mut StdRng) -> Vec<usize> {
        let mut ordering                = Vec::new();               // elimination ordering
        let mut mindeg: usize           = self.n;                   // current min degree
        let mut degree: Vec<usize>      = vec![0; self.n];          // current degree of each vertex
        let mut degmap: Vec<Vec<usize>> = vec![Vec::new(); self.n]; // lazy list of vertices of given degree
        
        // insert vertices to degree-map
        for v in 0..self.n {
            degree[v] = self.neighbors[v].len();
            degmap[degree[v]].push(v);
            if degree[v] < mindeg { mindeg = degree[v]; }
        }

        // compute the elimination ordering
        let mut eliminated = BitSet::new();
        let mut step = 0;
        while ordering.len() != self.n {
            step += 1;
            if step % 100 == 0 {
                // println!("Picking next. {}", step);
            }
            
            // pick a vertex of minimum degree at random
            if let Some(v) = random_pop(&mut degmap[mindeg], rng) {
                if degree[v] != mindeg    { continue; } // degree of v has changed
                if eliminated.contains(v) { continue; } // vertex already removed

                eliminated.insert(v);
                ordering.push(v);
                self.eliminate_vertex(v);
                
                // let now = Instant::now();
                for &w in self.neighbors[v].iter() {
                    degree[w] = self.neighbors[w].len();
                    degmap[degree[w]].push(w);
                    if degree[w] < mindeg { mindeg = degree[w]; }
                }
                // println!("{}", now.elapsed().as_micros());
            }

            // finished processing all vertices of mindeg
            if degmap[mindeg].is_empty() { mindeg += 1; }
        }

        ordering
    }

    /// Compute a tree decomposition of this graph and the given vertex ordering.
    ///
    /// *Assumes:*
    /// - that the ordering was computed using @see compute_peo
    /// - that the graph is connected (otherwise this will most likely fail and return None)
    ///
    pub fn peo_to_decomposition(&self, ordering: &[usize]) -> Option<Decomposition> {
        let mut td  = vec![(0, Vec::new()); self.n];
        
        // reverse index of ordering
        let mut index = vec![0; self.n];
        for (i,&v) in ordering.iter().enumerate() {
            index[v] = i;
        }

        // create a bag for the last vertex in the ordering
        let last_vertex = ordering[self.n-1];
        td[last_vertex].0 = last_vertex;
        td[last_vertex].1.push(last_vertex);

        // recursively build up the tree decomposition
        for i in (0..self.n-1).rev() {
            let v_i = ordering[i];
            let   j = self.neighbors[v_i].iter().map(|&w| index[w]).min()?;
            let v_j = ordering[j];

            for &w in self.neighbors[v_i].iter() { td[v_i].1.push(w); }
            td[v_i].1.push(v_i);
            td[v_i].0 = v_j;
        }
        
        // done
        Some(td)
    }
    
}

/// Picks and returns a random element from the given vector.
/// Returns None if the vector is empty.
///
fn random_pop(vec: &mut Vec<usize>, rng: &mut StdRng) -> Option<usize> {
    if let Some((index, &element)) = vec.iter().enumerate().choose(rng) {
        vec.swap_remove(index);
        return Some(element);
    }
    None
}

/// Reads a graph from stdin.
/// The format is assumed to be the PACE 2017 graph format.
///
fn _graph_from_stdin() -> anyhow::Result<Graph> {
    let mut g = None;
    for line in io::stdin().lock().lines() {
        let line = line?;
        let ll   = line.split(' ').collect::<Vec<&str>>();
        match ll[0] {
            "c" => continue, // ignore comments
            "p" => {         // extract universe size from p-line (generate graph)
                let n = ll[2].parse::<usize>()?;
                    g = Some(Graph::new(n));
            },
            _ => {           // parse edges and add them to the graph
                let u = ll[0].parse::<usize>()? - 1;
                let v = ll[1].parse::<usize>()? - 1;
                match g {
                    Some(ref mut g) => g.add_edge(u,v),
                    None    => bail!("c an edge appeared before the p-line -> abort!")
                }
            }
        }
    }
    match g {
        Some(g) => Ok(g),
        None    => bail!("c input had no p-line -> abort!")
    }
}

fn _main() {
    // get programm arguments
    let args: HashSet<String> = std::env::args().collect();
    
    // get graph from stdin
    let now = Instant::now();
    let mut g = match _graph_from_stdin() {
        Ok(g)  => g,
        Err(e) => {
            println!("{}", e);
            std::process::exit(1);
        }
    };
    println!("c used {} seconds to read the graph with {} vertices and {} edges",
             now.elapsed().as_secs(),
             g.n,
             (0..g.n).map(|v| g.neighbors[v].len()).sum::<usize>()/2
    );
    println!("c maximum degree: {}", (0..g.n).map(|v| g.neighbors[v].len()).max().or(Some(0)).unwrap());

    // random number generator to break ties
    let mut rng = StdRng::seed_from_u64(SEED);

    // compute peo and tree decomposition
    let now = Instant::now();
    let peo   = g.compute_peo(&mut rng);
    println!("c used {} seconds compute a peo", now.elapsed().as_secs());

    let now = Instant::now();
    let td    = match g.peo_to_decomposition(&peo) {
        Some(td) => td,
        None     => {
            println!("c failed to compute tree decomposition. The graph was probably not connected!");
            println!("c printing a trivial decomposition now");
            vec![(0, (0..g.n).collect())]
        }
    };
    println!("c used {} seconds to compute the tree decomposition", now.elapsed().as_secs());
    let width = td.iter().map(|(_,bag)| bag.len()).max().unwrap();
    
    // print s-line
    println!("s td {} {} {}", td.len(), width, g.n);

    // eventuall skip output of decomposition
    if args.contains(&String::from("-v")) { std::process::exit(0); }
    
    //print bags
    for (i, (_, bag)) in td.iter().enumerate() {
        print!("b {}", i+1);
        for v in bag { print!(" {}", v+1); }
        println!();
    }
    
    // print edges of tree decomposition
    for (i, (parent, _)) in td.iter().enumerate() {
        if i != *parent {
            println!("{} {}", i+1, parent+1);
        }
    }
}

pub fn print(td: &Decomposition, tw: usize, n: usize) -> String {
    let mut output = String::new();
    output.push_str(&format!("s td {} {} {}\n", td.len(), tw, n));
    for (i, (_, bag)) in td.iter().enumerate() {
        output.push_str(&format!("b {}", i));
        for node in bag {
            output.push_str(&format!(" {}", node));
        }
        output.push_str("\n");
    }

    for (i, &(parent, _)) in td.iter().enumerate() {
        if i < parent {
            output.push_str(&format!("{} {}\n", i, parent));
        } else if i > parent {
            output.push_str(&format!("{} {}\n", parent, i));
        }
    }

    output
}

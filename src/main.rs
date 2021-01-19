use egg::{rewrite as rw, *};
use std::collections::{HashMap, HashSet};

use itertools::Itertools;

define_language! {
    pub enum Datalog {
        Num(i32), // 0 is empty set
        "+" = Add([Id; 2]),
        "*" = Mul([Id; 2]),
        Symbol(egg::Symbol),
    }
}

fn rules() -> Vec<Rewrite<Datalog, ()>> {
    vec![
        rw!("add-0-l"; "(+ ?x 0)" => "?x"),
        rw!("add-0-lr"; "(+ ?y ?x)" => "(+ ?x ?y)"),
        rw!("mul-0-l"; "(* ?x 0)" => "0"),
        rw!("mul-0-r"; "(* 0 ?x)" => "0"),
        rw!("mul-0-lr"; "(* 0 ?x)" => "(* ?x 0)"),
        rw!("mul-0-rl"; "(* ?x 0)" => "(* 0 ?x)"),
    ]
}

fn main() {
    // initial egraph
    let mut egraph0 = EGraph::default();
    egraph0.add_expr(&"(+ e (* e r0))".parse().unwrap());
    let zero = egraph0.add_expr(&"0".parse().unwrap());
    let r = egraph0.add_expr(&"r0".parse().unwrap());
    egraph0.union(zero, r);
    let runner = Runner::default().with_egraph(egraph0).run(&rules());
    let egraph0 = runner.egraph;
    egraph0.dot().to_png("target/start.png").unwrap();

    // take one iter
    let mut egraph1 = egraph0.clone();
    let p0 = egraph1.add_expr(&"(+ e (* e r0))".parse().unwrap());
    let r1 = egraph1.add_expr(&"r1".parse().unwrap());
    egraph1.union(p0, r1);
    egraph1.add_expr(&"(+ e (* e r1))".parse().unwrap());
    let runner = Runner::default().with_egraph(egraph1).run(&rules());
    let egraph1 = runner.egraph;
    egraph1.dot().to_png("target/step.png").unwrap();

    let egraph = intersect(&egraph0, &egraph1, ());
    egraph.dot().to_png("target/inter.png").unwrap();

    // middle egraph
    let mut egraph2 = EGraph::default();
    egraph2.add_expr(&"(+ e (* e r1))".parse().unwrap());
    let zero = egraph2.add_expr(&"0".parse().unwrap());
    let r = egraph2.add_expr(&"r1".parse().unwrap());
    egraph2.union(zero, r);
    let runner = Runner::default().with_egraph(egraph2).run(&rules());
    let egraph2 = runner.egraph;
    egraph2.dot().to_png("target/middle.png").unwrap();

    let egraph = intersect(&egraph2, &egraph1, ());
    egraph.dot().to_png("target/sect.png").unwrap();
}

fn intersect<L, A>(g1: &EGraph<L, A>, g2: &EGraph<L, A>, analysis: A) -> EGraph<L, A>
where
    L: Language,
    A: Analysis<L>,
{
    let mut g = EGraph::new(analysis);
    let mut e1: HashSet<Id> = HashSet::new();
    let mut e1_e: HashMap<Id, HashSet<Id>> = HashMap::new();
    let mut e_e2: HashMap<Id, Id> = HashMap::new();
    let empty_set = HashSet::new();
    loop {
        let mut g_changed = false;
        for class in g1.classes() {
            for node in &class.nodes {
                if node.children().iter().all(|c| e1.contains(c)) {
                    for mut n_new in flatmap_children(node, |id| {
                        e1_e.get(&id).unwrap_or(&empty_set).iter().copied()
                    }) {
                        if let Some(c2) = g2.lookup(n_new.clone().map_children(|id| e_e2[&id])) {
                            let c_new = g.lookup(&mut n_new).unwrap_or_else(|| {
                                g_changed = true;
                                e1.insert(class.id);
                                g.add(n_new.clone())
                            });
                            e_e2.insert(c_new, c2);
                            e1_e.entry(class.id).or_insert(HashSet::new()).insert(c_new);
                            for c in e1_e[&class.id].iter() {
                                if g2.find(e_e2[&c]) == g2.find(c2) {
                                    let unioned = g.union(c_new, *c).1;
                                    g_changed = g_changed || unioned;
                                    g.rebuild();
                                }
                            }
                        }
                    }
                }
            }
        }
        if !g_changed {
            break;
        }
    }
    g
}

// compute the set of new nodes op(c1',...,cn') from op(c1,...,cn)
// let op(c1,...,cn) = node;
// vec![op(c1',...,cn') where c1' in f(c1),...,cn' in f(cn)]
fn flatmap_children<L, F, I>(node: &L, f: F) -> Vec<L>
where
    L: Language,
    I: Clone + Iterator<Item = Id>,
    F: Fn(Id) -> I,
{
    if node.children().is_empty() {
        vec![node.clone()]
    } else {
        let childrens = node
            .children()
            .iter()
            .map(|id| f(*id))
            .multi_cartesian_product();
        childrens
            .map(|children| {
                let mut new_node = node.clone();
                for i in 0..children.len() {
                    new_node.children_mut()[i] = children[i];
                }
                new_node
            })
            .collect()
    }
}

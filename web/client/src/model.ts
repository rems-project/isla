// This interfaces in file correspond to server/src/request.rs

export interface ModelEvent {
    opcode: string
    po: number
    thread_id: number
    name: string
}

export interface ModelSet {
    name: string
    elems: string[]
}

export interface ModelRel {
    name: string
    edges: string[][]
}

export interface ModelGraph {
    events: ModelEvent[]
    sets: ModelSet[]
    relations: ModelRel[]
    show: string[]
}

function relationColor(rel: string): string {
    if (rel == 'rf') {
        return 'crimson'
    } else if (rel == 'co') {
        return 'goldenrod'
    } else {
        return 'black'
    }
}

function relationExtra(rel: string): string {
    if (rel == 'co') {
        return ',constraint=true'
    } else {
        return ',constraint=false'
    }
}

export class Model {
    graphs: ModelGraph[]
    current: ModelGraph
    draw: string[]

    constructor(graphs: ModelGraph[]) {
        this.graphs = graphs
        this.current = graphs[0]
        this.draw = ['rf', 'co']
    }

    graphviz(): string {
        var g = 'digraph Exec {\n';

        let threads = new Set<number>()
        this.current.events.forEach(ev => {
            threads.add(ev.thread_id)
        });

        for(let thread of threads.values()) {
            g += `  subgraph cluster${thread} {\n`
            g += `    label="Thread #${thread}"\n`

            let evs = this.current.events.filter(ev => ev.thread_id == thread)
            evs.forEach(ev => {
                g += `    ${ev.name} [label="${ev.name}\\l${ev.opcode}"];\n`
            })
            g += '    '
            for (var i: number = 0; i < evs.length; i++) {
                let ev = evs[i]
                let last = (i == evs.length - 1)
                g += ev.name + (last ? ';\n' : ' -> ')
            }
            g += '  }\n'
        }
        g += '  IW [label="Initial State",shape=hexagon]\n'

        this.draw.forEach(to_draw => {
            this.current.relations.forEach(rel => {
                if (rel.name == to_draw) {
                    let color = relationColor(rel.name)
                    let extra = relationExtra(rel.name)
                    rel.edges.forEach(edge => {
                        g += `  ${edge[0]} -> ${edge[1]} [color=${color},label="${rel.name}"${extra}]\n`
                    })
                }
            })
        })

        g += '}\n'
        return g
    }
}

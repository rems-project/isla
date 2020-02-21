// This interfaces in file correspond to server/src/request.rs

export interface ModelEvent {
    // Can be null if we can't parse the objdump to find the opcode
    instr: string | null
    opcode: string
    po: number
    thread_id: number
    name: string
    value: string | null
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
    } else if (rel == 'fr') {
        return 'limegreen'
    } else if (rel == 'addr') {
        return 'blue2'
    } else if (rel == 'data') {
        return 'darkgreen'
    } else if (rel == 'ctrl') {
        return 'darkorange2'
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
        this.draw = ['rf', 'co', 'fr', 'addr', 'data', 'ctrl']
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
            g += '    style=dashed\n'
            g += '    color=gray50\n'

            let evs = this.current.events.filter(ev => ev.thread_id == thread)
            evs.forEach(ev => {
                // If instr is null, use the raw opcode instead
                let instr = ev.instr ? ev.instr : ev.opcode
                if (ev.value) {
                   g += `    ${ev.name} [label="${instr}\\l${ev.value}"];\n`
                } else {
                   g += `    ${ev.name} [label="${instr}"];\n`
                }
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
                        // The extra padding around label helps space out the graph
                        g += `  ${edge[0]} -> ${edge[1]} [color=${color},label="${rel.name}"${extra},fontcolor=${color}]\n`
                    })
                }
            })
        })

        g += '}\n'
        return g
    }
}

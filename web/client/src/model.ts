// BSD 2-Clause License
//
// Copyright (c) 2020 Victor Gomes
// Copyright (c) 2020 Alasdair Armstrong
//
// All rights reserved.
//
// Redistribution and use in source and binary forms, with or without
// modification, are permitted provided that the following conditions are
// met:
// 
// 1. Redistributions of source code must retain the above copyright
// notice, this list of conditions and the following disclaimer.
// 
// 2. Redistributions in binary form must reproduce the above copyright
// notice, this list of conditions and the following disclaimer in the
// documentation and/or other materials provided with the distribution.
// 
// THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
// "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
// LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
// A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
// HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
// SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
// LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
// DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
// THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
// (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
// OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

import { Options } from './common'

export interface ModelRel {
    name: string
    dot: string
}

export interface ModelGraph {
    prefix: string
    relations: ModelRel[]
    suffix: string
}

export class Model {
    graphs: ModelGraph[]
    currentIndex: number
    current: ModelGraph
    draw: Set<string>
    
    constructor(graphs: ModelGraph[], draw: string[], opts: Options) {
        this.graphs = graphs
        this.currentIndex = 0
        this.current = graphs[0]
        this.draw = new Set(draw)
    }

    nextGraph() {
        this.currentIndex = (this.currentIndex + 1) % this.graphs.length
        this.current = this.graphs[this.currentIndex]
        return this.currentIndex + 1
    }

    prevGraph() {
        this.currentIndex = this.currentIndex - 1
        if (this.currentIndex < 0) {
            this.currentIndex = this.graphs.length - 1
        }
        this.current = this.graphs[this.currentIndex]
        return this.currentIndex + 1
    }

    relations(): string[] {
        return this.current.relations.map(ev => ev.name)
    }

    graphviz(): string {
        var g = '';

        g += this.current.prefix;

        this.draw.forEach(to_draw => {
            this.current.relations.forEach(rel => {
                if (rel.name == to_draw) {
                    g += rel.dot
                }
            })
        })

        g += this.current.suffix;

        return g
    }
}

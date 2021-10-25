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

import $ from 'jquery'
import * as util from './util'
import UI from './ui'
import { Arch } from './common'

export namespace Widget {

export abstract class Widget {
  dom: JQuery<HTMLElement>
  body: JQuery<HTMLElement>
  constructor (title: string) {
    const cancel = $('<div class="menu-item btn">Cancel</div></li>')
    cancel.on('click', () => this.hide ())
    const headerContent = $('<ul class="menu x-fill">')
    headerContent.append($(`<li><div class="title">${title}</div></li>`))
    headerContent.append($('<li class="right">').append(cancel))
    const header = $('<div class="header">')
    header.append(headerContent)

    this.body = $('<div class="widget_body">')
    this.dom = $('<div class="widget invisible">')
    this.dom.append(header)
    this.dom.append(this.body)
    $(document.body).append(this.dom)
  }
  fetch_test(dir: string, litmus_name: string, cat_name: string, arch: Arch) {
    util.get2(dir+'/'+litmus_name, cat_name, (litmus: string, cat: string) => {
      this.hide()
      UI.addView(litmus_name, litmus, cat_name, cat, arch)
    })
  }
  show() {
    this.dom.removeClass('invisible')
  }
  hide() {
    this.dom.addClass('invisible')
  }
}

export class AArch64 extends Widget {
  constructor () {
    super('Load basic AArch64 tests')
    util.get('aarch64.json', (data: any) => {
      for (let i = 0; i < data.length; i++) {
        const tests = $('<ul class="tests"></ul>')
        for (let k = 0; data[i].tests && k < data[i].tests.length; k++) {
          const name = data[i].tests[k]
          const link = $(`<a href="#">${name}</a>`)
          link.on('click', () => {
            this.fetch_test('aarch64', name, data[i].model, Arch.AArch64)
            UI.getView().state.options.ignore_ifetch = true
          })
          const test = $('<li>')
          test.append(link)
          tests.append(test)
        }
        this.body.append($('<h3>'+data[i].section+'</h3>'))
        this.body.append(tests)
      }
      this.show()
    })
  }
}

export class RISCV64 extends Widget {
  constructor () {
    super('Load basic RISC-V tests')
    util.get('riscv64.json', (data: any) => {
      for (let i = 0; i < data.length; i++) {
        const tests = $('<ul class="tests"></ul>')
        for (let k = 0; data[i].tests && k < data[i].tests.length; k++) {
          const name = data[i].tests[k]
          const link = $(`<a href="#">${name}</a>`)
          link.on('click', () => {
            this.fetch_test('riscv64', name, data[i].model, Arch.RISCV64)
            UI.getView().state.options.ignore_ifetch = true
          })
          const test = $('<li>')
          test.append(link)
          tests.append(test)
        }
        this.body.append($('<h3>'+data[i].section+'</h3>'))
        this.body.append(tests)
      }
      this.show()
    })
  }
}

export class ESOP2020 extends Widget {
  constructor () {
    super('Load ESOP 2020 instruction fetch tests')
    util.get('esop2020.json', (data: any) => {
      for (let i = 0; i < data.length; i++) {
        const tests = $('<ul class="tests"></ul>')
        for (let k = 0; data[i].tests && k < data[i].tests.length; k++) {
          const name = data[i].tests[k]
          const link = $(`<a href="#">${name}</a>`)
          link.on('click', () => {
            this.fetch_test('ifetch', name, data[i].model, Arch.AArch64)
            UI.getView().state.options.ignore_ifetch = false
          })
          const test = $('<li>')
          test.append(link)
          tests.append(test)
        }
        this.body.append($('<h3>'+data[i].section+'</h3>'))
        this.body.append(tests)
      }
      this.show()
    })
  }
}

export class AArch64VMSA extends Widget {
  constructor () {
    super('Load AArch64 VMSA tests')
    util.get('aarch64-vmsa.json', (data: any) => {
      for (let i = 0; i < data.length; i++) {
        const tests = $('<ul class="tests"></ul>')
        for (let k = 0; data[i].tests && k < data[i].tests.length; k++) {
          const name = data[i].tests[k]
          const link = $(`<a href="#">${name}</a>`)
          link.on('click', () => {
            this.fetch_test('aarch64-vmsa', name, data[i].model, Arch.AArch64VMSA)
            UI.getView().state.options.ignore_ifetch = true
            UI.getView().state.options.armv8_page_tables = true
          })
          const test = $('<li>')
          test.append(link)
          tests.append(test)
        }
        this.body.append($('<h3>'+data[i].section+'</h3>'))
        this.body.append(tests)
      }
      this.show()
    })
  }
}

}

export default Widget
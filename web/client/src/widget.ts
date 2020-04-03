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
  fetch_test(dir: string, litmus_name: string, cat_name: string) {
    util.get2(dir+'/'+litmus_name, cat_name, (litmus: string, cat: string) => {
      this.hide()
      UI.addView(litmus_name, litmus, cat_name, cat, Arch.AArch64)
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
            this.fetch_test('aarch64', name, data[i].model)
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
            this.fetch_test('ifetch', name, data[i].model)
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

}

export default Widget
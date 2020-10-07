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
import _ from 'lodash'
import './css/scheme.css'
import './css/goldenlayout-base.css'
import './css/goldenlayout-light-theme.css'
import './css/codemirror.css'
import './css/style.css'
import './css/midnight.css'
import GoldenLayout from 'golden-layout'
import UI from './ui'
import { get2 } from './util'
import { Arch } from './common'
import './js/herd.js'
import './js/toml.js'
import './js/panzoom.js'

type StartupMode =
  { kind: 'default' } |
  { kind: 'permalink', config: any } |
  { kind: 'fixedlink', litmus: string, cat: string, arch: Arch }

function litmus_name(str: string) {
    return /^([a-zA-Z0-9_.+-])*$/.test(str)
}

function parseFixedLink(arch_spec: string, test: string): StartupMode {
  if (test.includes('/') || test.includes('..') || !litmus_name(test)) {
    return { kind: 'default' }
  }

  if (arch_spec == 'rv32') {
    return {
      kind: 'fixedlink',
      litmus: 'riscv64/' + test + '.toml',
      cat: 'riscv.cat',
      arch: Arch.RISCV32
    }
  } else if (arch_spec == 'rv64') {
    return {
      kind: 'fixedlink',
      litmus: 'riscv64/' + test + '.toml',
      cat: 'riscv.cat',
      arch: Arch.RISCV64
    }
  } else if (arch_spec == 'aarch64') {
    return {
      kind: 'fixedlink',
      litmus: 'aarch64/' + test + '.toml',
      cat: 'aarch64.cat',
      arch: Arch.AArch64,
    }
  } else {
    return { kind: 'default' }
  }
}

function getStartupMode(): StartupMode {
  try {
    // First try a permanent link
    let uri = document.URL.split('#')
    if (uri && uri.length == 2 && uri[1] !== '') {
      const config = GoldenLayout.unminifyConfig(JSON.parse(decodeURIComponent(uri[1])))
      return {
        kind: 'permalink',
        config: config,
      }
    }

    // Fixed link
    uri = document.URL.split('?')
    if (uri && uri.length == 2 && uri[1] !== '') {
      let query = uri[1].split(/_(.+)/)
      if (query && query.length >= 2) {
        return parseFixedLink(query[0], query[1])
      }
    }

    // Default
    return { kind: 'default'}
  } catch (e) {
    console.log(`Startup error: ${e}`)
    return { kind: 'default'}
  }
}

function defaultStart() {
  get2('aarch64/MP.toml', 'aarch64.cat', (litmus: string, cat: string, isla_config: string) => {
    UI.addView('MP.toml', litmus, 'aarch64.cat', cat, Arch.AArch64, isla_config)
  }, () => {
    console.log('Error when trying to download "MP.toml"... Using an empty file.')
    UI.addView('example.toml', '', '', '', Arch.AArch64, '')
  })
}

function fixedStart(arch: Arch, litmus_name: string, cat_name: string) {
  get2(litmus_name, cat_name, (litmus: string, cat: string, isla_config: string) => {
    UI.addView(litmus_name.split('/')[1], litmus, cat_name, cat, arch, isla_config)
  }, () => {
    console.log('Error when trying to load fixed link')
    UI.addView('example.toml', '', '', '', Arch.AArch64, '')
  })
}

export function onLoad() {
  const mode = getStartupMode()
  switch (mode.kind) {
    case 'default':
      defaultStart()
      break
    case 'fixedlink':
      fixedStart(mode.arch, mode.litmus, mode.cat)
      break
    case 'permalink':
      UI.addView(mode.config.litmus_name, mode.config.litmus, mode.config.cat_name, mode.config.cat, mode.config.arch, mode.config)
      break
  }
}

$(window).ready(onLoad)

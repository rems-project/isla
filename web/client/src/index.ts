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

function getStartupMode(): StartupMode {
  try {
    // First try a permanent link
    let uri = document.URL.split('#')
    if (uri && uri.length == 2 && uri[1] !== '') {
      const config = GoldenLayout.unminifyConfig(JSON.parse(decodeURIComponent(uri[1])))
      return { kind: 'permalink',
              config: config,
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

export function onLoad() {
  const mode = getStartupMode()
  switch (mode.kind) {
    case 'default':
      defaultStart()
      break
    case 'permalink':
      UI.addView(mode.config.litmus_name, mode.config.litmus, mode.config.cat_name, mode.config.cat, mode.config.arch, mode.config)
      break
  }
}

$(window).ready(onLoad)

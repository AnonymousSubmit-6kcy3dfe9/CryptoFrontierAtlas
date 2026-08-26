// Keeps the app type-checkable with older React DOM declaration packages;
// the published build also installs @types/react-dom.
declare module 'react-dom/client' {
  import type { ReactNode } from 'react';

  interface Root {
    render(children: ReactNode): void;
  }

  export function createRoot(container: Element | DocumentFragment): Root;
}

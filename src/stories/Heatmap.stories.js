import React from 'react';
import { storiesOf } from '@storybook/react';

import App from '../lib';

const stories = storiesOf('Heatmap', module);

stories.add('Main', () => {
  return <App />
});
import React, { useState } from 'react';
import { format } from 'date-fns';
import locale from 'date-fns/esm/locale/pt-BR';

import { Container, Tooltip } from './styles';

const Box = ({
  date,
  color,
  value,
  marginTop,
  showTooltip: showTooltipProps,
  boxShape,
  onClick = () => { }
}) => {

  const [showTooltip, setShowTooltip] = useState(false);

  return (
    <Container
      onClick={() => onClick(date, value)}
      onMouseEnter={() => setShowTooltip(true)}
      onMouseLeave={() => setShowTooltip(false)}
      style={{
        marginTop,
        backgroundColor: color,
        cursor: value ? 'pointer' : '',
        borderRadius: boxShape === 'circle' ? '50%' : 0
      }}>
      {
        showTooltipProps && showTooltip &&
        <Tooltip>
          {
            date &&
            <span>{format(date, 'PP', {
              locale
            })}{value && <span style={{ marginRight: 2 }}>:</span>}</span>
          }
          {value && <span> {value}</span>}
        </Tooltip>
      }
    </Container>
  )
}

export default Box;
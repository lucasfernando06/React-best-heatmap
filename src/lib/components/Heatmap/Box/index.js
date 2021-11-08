import React from 'react';
import { format } from 'date-fns';
import { usePopperTooltip } from "react-popper-tooltip";
import { Container } from './styles';

const Box = ({
  box,
  legend,
  locale,
  marginTop,
  showTooltip,
  boxShape
}) => {

  const {
    getArrowProps,
    getTooltipProps,
    setTooltipRef,
    setTriggerRef,
    visible
  } = usePopperTooltip();

  const { date, value, valueLabel, color, onClick } = box;

  const getColor = () => (legend && legend.find(l => l.isInRange(value))?.color) || '#ebedf0';

  const label = valueLabel ? valueLabel : value;
  const finalColor = color ? color : getColor();

  return (
    <Container
      ref={setTriggerRef}
      onClick={() => onClick && onClick(date, value)}
      style={{
        marginTop,
        backgroundColor: finalColor,
        cursor: value ? 'pointer' : '',
        borderRadius: boxShape === 'circle' ? '50%' : 0
      }}>
      {
        showTooltip && visible &&
        <div ref={setTooltipRef} {...getTooltipProps({
          className: "tooltip-container",
          style: {
            background: 'rgba(0, 0, 0, .75)',
            color: '#fff',
            minWidth: 100,
            textAlign: 'center'
          }
        })}>
          {
            label ? (
              <span>{label}</span>
            ) : (
              date && locale &&
              <span>{format(date, 'PP', {
                locale
              })}{value && <span style={{ marginRight: 2 }}>:</span>}</span>
            )
          }
          <div {...getArrowProps({
            className: "tooltip-arrow", style: {
              border: 'black', '--tooltipBackground': 'rgba(0, 0, 0, .75)'
            }
          })} />
        </div>
      }
    </Container>
  )
}

export default Box;